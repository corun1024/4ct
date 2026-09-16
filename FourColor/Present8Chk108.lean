import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 108 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5388l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5388l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5388l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5388l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5393_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5393 :
    hubcapFit theRedpart rf8 p8_5388l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5393_1, c8_5393_2, c8_5393_3, c8_5393_4, c8_5393_5, c8_5393_6, c8_5393_7, c8_5393_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5395_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5395 :
    hubcapFit theRedpart rf8 p8_5374l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5395_1, c8_5395_2, c8_5395_3, c8_5395_4, c8_5395_5, c8_5395_6, c8_5395_7, c8_5395_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5373l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5373l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5373l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5373l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5397_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5397 :
    hubcapFit theRedpart rf8 p8_5373l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5397_1, c8_5397_2, c8_5397_3, c8_5397_4, c8_5397_5, c8_5397_6, c8_5397_7, c8_5397_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5403r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5403r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5403r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5403r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5403r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5403r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5404_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5403r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5404 :
    hubcapFit theRedpart rf8 p8_5403r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5404_1, c8_5404_2, c8_5404_3, c8_5404_4, c8_5404_5, c8_5404_6, c8_5404_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5403l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5403l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5403l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5403l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5403l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5403l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5405_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5403l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5405 :
    hubcapFit theRedpart rf8 p8_5403l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5405_1, c8_5405_2, c8_5405_3, c8_5405_4, c8_5405_5, c8_5405_6, c8_5405_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5402l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5402l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5402l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5402l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5402l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5402l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5407_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5402l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5407 :
    hubcapFit theRedpart rf8 p8_5402l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5407_1, c8_5407_2, c8_5407_3, c8_5407_4, c8_5407_5, c8_5407_6, c8_5407_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5401l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5401l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5401l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5401l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5409_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5401l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5409 :
    hubcapFit theRedpart rf8 p8_5401l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5409_1, c8_5409_2, c8_5409_3, c8_5409_4, c8_5409_5, c8_5409_6, c8_5409_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5369l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5369l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5369l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5369l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5369l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5369l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5412_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5369l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5412 :
    hubcapFit theRedpart rf8 p8_5369l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5412_1, c8_5412_2, c8_5412_3, c8_5412_4, c8_5412_5, c8_5412_6, c8_5412_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5415r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5415r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5415r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5415r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5415r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5415r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5416_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5415r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5416 :
    hubcapFit theRedpart rf8 p8_5415r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5416_1, c8_5416_2, c8_5416_3, c8_5416_4, c8_5416_5, c8_5416_6, c8_5416_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5415l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5415l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5417_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5417 :
    hubcapFit theRedpart rf8 p8_5415l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5417_1, c8_5417_2, c8_5417_3, c8_5417_4, c8_5417_5, c8_5417_6, c8_5417_7, c8_5417_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5367l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5367l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5367l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5367l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5367l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5419_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5367l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5419 :
    hubcapFit theRedpart rf8 p8_5367l
    (Hubcap.one 0 1 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5419_1, c8_5419_2, c8_5419_3, c8_5419_4, c8_5419_5, c8_5419_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5366l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5366l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5366l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5366l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5366l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5421_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5366l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5421 :
    hubcapFit theRedpart rf8 p8_5366l
    (Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5421_1, c8_5421_2, c8_5421_3, c8_5421_4, c8_5421_5, c8_5421_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5428r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5428r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5428r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5428r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5428r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5429_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5429 :
    hubcapFit theRedpart rf8 p8_5428r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5429_1, c8_5429_2, c8_5429_3, c8_5429_4, c8_5429_5, c8_5429_6, c8_5429_7, c8_5429_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5428l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5428l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5428l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5428l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5428l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5428l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5430_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5430 :
    hubcapFit theRedpart rf8 p8_5428l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5430_1, c8_5430_2, c8_5430_3, c8_5430_4, c8_5430_5, c8_5430_6, c8_5430_7, c8_5430_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5425l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5425l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5425l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5425l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5432_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5425l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5432 :
    hubcapFit theRedpart rf8 p8_5425l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5432_1, c8_5432_2, c8_5432_3, c8_5432_4, c8_5432_5, c8_5432_6]

end FourColor

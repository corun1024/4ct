import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 89 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4411l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4446_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4411l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4446 :
    hubcapFit theRedpart rf8 p8_4411l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4446_1, c8_4446_2, c8_4446_3, c8_4446_4, c8_4446_5, c8_4446_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4364l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4364l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4364l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4364l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4364l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4449_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4364l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4449 :
    hubcapFit theRedpart rf8 p8_4364l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4449_1, c8_4449_2, c8_4449_3, c8_4449_4, c8_4449_5, c8_4449_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4451_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4224l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4451_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4224l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4451_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4224l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4451_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4224l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4451_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4224l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4451 :
    hubcapFit theRedpart rf8 p8_4224l
    (Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4451_1, c8_4451_2, c8_4451_3, c8_4451_4, c8_4451_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4452_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4223l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4452_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4452_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4223l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4452_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4223l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4452_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4223l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4452 :
    hubcapFit theRedpart rf8 p8_4223l
    (Hubcap.one 0 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4452_1, c8_4452_2, c8_4452_3, c8_4452_4, c8_4452_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4462r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4462r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4462r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4462r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4462r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4462r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4463_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4462r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4463 :
    hubcapFit theRedpart rf8 p8_4462r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4463_1, c8_4463_2, c8_4463_3, c8_4463_4, c8_4463_5, c8_4463_6, c8_4463_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4462l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4464_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4462l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4464 :
    hubcapFit theRedpart rf8 p8_4462l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4464_1, c8_4464_2, c8_4464_3, c8_4464_4, c8_4464_5, c8_4464_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4473r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4473r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4473r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4473r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4473r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4473r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4474_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4473r) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4474 :
    hubcapFit theRedpart rf8 p8_4473r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4474_1, c8_4474_2, c8_4474_3, c8_4474_4, c8_4474_5, c8_4474_6, c8_4474_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4473l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4475_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4473l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4475 :
    hubcapFit theRedpart rf8 p8_4473l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4475_1, c8_4475_2, c8_4475_3, c8_4475_4, c8_4475_5, c8_4475_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4477_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4477 :
    hubcapFit theRedpart rf8 p8_4472l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4477_1, c8_4477_2, c8_4477_3, c8_4477_4, c8_4477_5, c8_4477_6, c8_4477_7, c8_4477_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4471l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4471l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4479_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4471l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4479 :
    hubcapFit theRedpart rf8 p8_4471l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4479_1, c8_4479_2, c8_4479_3, c8_4479_4, c8_4479_5, c8_4479_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4469l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4481_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4469l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4481 :
    hubcapFit theRedpart rf8 p8_4469l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4481_1, c8_4481_2, c8_4481_3, c8_4481_4, c8_4481_5, c8_4481_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4467l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4467l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4483_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4467l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4483 :
    hubcapFit theRedpart rf8 p8_4467l
    (Hubcap.one 0 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4483_1, c8_4483_2, c8_4483_3, c8_4483_4, c8_4483_5, c8_4483_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4466l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4466l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4466l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4466l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4466l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4466l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4484_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4466l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4484 :
    hubcapFit theRedpart rf8 p8_4466l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4484_1, c8_4484_2, c8_4484_3, c8_4484_4, c8_4484_5, c8_4484_6, c8_4484_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4492r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4492r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4492r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4492r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4492r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4492r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4492r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4493_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4492r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4493 :
    hubcapFit theRedpart rf8 p8_4492r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4493_1, c8_4493_2, c8_4493_3, c8_4493_4, c8_4493_5, c8_4493_6, c8_4493_7, c8_4493_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4492l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4492l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4492l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4494_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4492l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4494 :
    hubcapFit theRedpart rf8 p8_4492l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4494_1, c8_4494_2, c8_4494_3, c8_4494_4, c8_4494_5, c8_4494_6, c8_4494_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4491l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4496_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4491l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4496 :
    hubcapFit theRedpart rf8 p8_4491l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4496_1, c8_4496_2, c8_4496_3, c8_4496_4, c8_4496_5, c8_4496_6, c8_4496_7]

end FourColor

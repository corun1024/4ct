import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 93 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4656r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4656r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4656r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4657_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4657 :
    hubcapFit theRedpart rf8 p8_4656r
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4657_1, c8_4657_2, c8_4657_3, c8_4657_4, c8_4657_5, c8_4657_6, c8_4657_7, c8_4657_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4656l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4656l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4658_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4656l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4658 :
    hubcapFit theRedpart rf8 p8_4656l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4658_1, c8_4658_2, c8_4658_3, c8_4658_4, c8_4658_5, c8_4658_6, c8_4658_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4654l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4654l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4654l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4654l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4654l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4660_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4654l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4660 :
    hubcapFit theRedpart rf8 p8_4654l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4660_1, c8_4660_2, c8_4660_3, c8_4660_4, c8_4660_5, c8_4660_6, c8_4660_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4653l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4653l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4653l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4653l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4653l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4653l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4662_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4653l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4662 :
    hubcapFit theRedpart rf8 p8_4653l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4662_1, c8_4662_2, c8_4662_3, c8_4662_4, c8_4662_5, c8_4662_6, c8_4662_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4652l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4652l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4652l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4652l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4652l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4652l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4664_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4652l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4664 :
    hubcapFit theRedpart rf8 p8_4652l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4664_1, c8_4664_2, c8_4664_3, c8_4664_4, c8_4664_5, c8_4664_6, c8_4664_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4651l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4651l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4651l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4651l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4666_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4651l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4666 :
    hubcapFit theRedpart rf8 p8_4651l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4666_1, c8_4666_2, c8_4666_3, c8_4666_4, c8_4666_5, c8_4666_6, c8_4666_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4650l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4650l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4650l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4650l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4650l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4650l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4668_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4650l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4668 :
    hubcapFit theRedpart rf8 p8_4650l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4668_1, c8_4668_2, c8_4668_3, c8_4668_4, c8_4668_5, c8_4668_6, c8_4668_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4649l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4649l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4649l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4670_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4670 :
    hubcapFit theRedpart rf8 p8_4649l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4670_1, c8_4670_2, c8_4670_3, c8_4670_4, c8_4670_5, c8_4670_6, c8_4670_7, c8_4670_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4648l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4648l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4648l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4648l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4672_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4648l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4672 :
    hubcapFit theRedpart rf8 p8_4648l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4672_1, c8_4672_2, c8_4672_3, c8_4672_4, c8_4672_5, c8_4672_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4647l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4647l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4647l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4647l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4673_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4673 :
    hubcapFit theRedpart rf8 p8_4647l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4673_1, c8_4673_2, c8_4673_3, c8_4673_4, c8_4673_5, c8_4673_6, c8_4673_7, c8_4673_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4682r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4682r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4682r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4682r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4682r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4682r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4683_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4682r) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4683 :
    hubcapFit theRedpart rf8 p8_4682r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4683_1, c8_4683_2, c8_4683_3, c8_4683_4, c8_4683_5, c8_4683_6, c8_4683_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4682l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4682l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4682l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4682l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4682l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4684_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4682l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4684 :
    hubcapFit theRedpart rf8 p8_4682l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4684_1, c8_4684_2, c8_4684_3, c8_4684_4, c8_4684_5, c8_4684_6, c8_4684_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4681l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4681l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4681l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4686_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4681l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4686 :
    hubcapFit theRedpart rf8 p8_4681l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4686_1, c8_4686_2, c8_4686_3, c8_4686_4, c8_4686_5, c8_4686_6, c8_4686_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4680l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4680l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4680l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4680l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4680l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4688_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4688 :
    hubcapFit theRedpart rf8 p8_4680l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4688_1, c8_4688_2, c8_4688_3, c8_4688_4, c8_4688_5, c8_4688_6, c8_4688_7, c8_4688_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4679l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4679l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4679l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4690_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4679l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4690 :
    hubcapFit theRedpart rf8 p8_4679l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4690_1, c8_4690_2, c8_4690_3, c8_4690_4, c8_4690_5, c8_4690_6]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 59 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2993l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2993l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2993l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2993l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2993l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2993l) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3008_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2993l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3008 :
    hubcapFit theRedpart rf8 p8_2993l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3008_1, c8_3008_2, c8_3008_3, c8_3008_4, c8_3008_5, c8_3008_6, c8_3008_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3010_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2992l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3010_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3010_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2992l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3010_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2992l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3010_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2992l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3010 :
    hubcapFit theRedpart rf8 p8_2992l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3010_1, c8_3010_2, c8_3010_3, c8_3010_4, c8_3010_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3011_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3011_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2991l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3011_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2991l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3011_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2991l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3011_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2991l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3011 :
    hubcapFit theRedpart rf8 p8_2991l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3011_1, c8_3011_2, c8_3011_3, c8_3011_4, c8_3011_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3013_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3013_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3013_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2990l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3013_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2990l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3013_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2990l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3013 :
    hubcapFit theRedpart rf8 p8_2990l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3013_1, c8_3013_2, c8_3013_3, c8_3013_4, c8_3013_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3022r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3022r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3022r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3022r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3022r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3023_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3022r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3023 :
    hubcapFit theRedpart rf8 p8_3022r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3023_1, c8_3023_2, c8_3023_3, c8_3023_4, c8_3023_5, c8_3023_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3022l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3024_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3022l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3024 :
    hubcapFit theRedpart rf8 p8_3022l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3024_1, c8_3024_2, c8_3024_3, c8_3024_4, c8_3024_5, c8_3024_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3021l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3021l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3021l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3021l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3021l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3026_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3021l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3026 :
    hubcapFit theRedpart rf8 p8_3021l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3026_1, c8_3026_2, c8_3026_3, c8_3026_4, c8_3026_5, c8_3026_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3020l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3020l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3020l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3027_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3020l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3027 :
    hubcapFit theRedpart rf8 p8_3020l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3027_1, c8_3027_2, c8_3027_3, c8_3027_4, c8_3027_5, c8_3027_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3029_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3019l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3029 :
    hubcapFit theRedpart rf8 p8_3019l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3029_1, c8_3029_2, c8_3029_3, c8_3029_4, c8_3029_5, c8_3029_6, c8_3029_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3031_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3018l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3031 :
    hubcapFit theRedpart rf8 p8_3018l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3031_1, c8_3031_2, c8_3031_3, c8_3031_4, c8_3031_5, c8_3031_6, c8_3031_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3017l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3017l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3017l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3033_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3017l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3033 :
    hubcapFit theRedpart rf8 p8_3017l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3033_1, c8_3033_2, c8_3033_3, c8_3033_4, c8_3033_5, c8_3033_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2965l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3035_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2965l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3035 :
    hubcapFit theRedpart rf8 p8_2965l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3035_1, c8_3035_2, c8_3035_3, c8_3035_4, c8_3035_5, c8_3035_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2964l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2964l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3037_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2964l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3037 :
    hubcapFit theRedpart rf8 p8_2964l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3037_1, c8_3037_2, c8_3037_3, c8_3037_4, c8_3037_5, c8_3037_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3038_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2963l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3038_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3038_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2963l) (hubSubn 8 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3038_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2963l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3038_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2963l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3038 :
    hubcapFit theRedpart rf8 p8_2963l
    (Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3038_1, c8_3038_2, c8_3038_3, c8_3038_4, c8_3038_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3057r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3057r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3057r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3057r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3057r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3057r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3058_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3057r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3058 :
    hubcapFit theRedpart rf8 p8_3057r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3058_1, c8_3058_2, c8_3058_3, c8_3058_4, c8_3058_5, c8_3058_6, c8_3058_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3057l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3057l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3057l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3059_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3057l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3059 :
    hubcapFit theRedpart rf8 p8_3057l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3059_1, c8_3059_2, c8_3059_3, c8_3059_4, c8_3059_5, c8_3059_6, c8_3059_7, c8_3059_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3055l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3055l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3061_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3055l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3061 :
    hubcapFit theRedpart rf8 p8_3055l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3061_1, c8_3061_2, c8_3061_3, c8_3061_4, c8_3061_5, c8_3061_6, c8_3061_7]

end FourColor

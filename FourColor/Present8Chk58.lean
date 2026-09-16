import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 58 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2955l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2955l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2955l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2955l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2955l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2955l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2957_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2955l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2957 :
    hubcapFit theRedpart rf8 p8_2955l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2957_1, c8_2957_2, c8_2957_3, c8_2957_4, c8_2957_5, c8_2957_6, c8_2957_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2954l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2954l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2954l) (hubSubn 8 7 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2954l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2954l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2959_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2954l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2959 :
    hubcapFit theRedpart rf8 p8_2954l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2959_1, c8_2959_2, c8_2959_3, c8_2959_4, c8_2959_5, c8_2959_6, c8_2959_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2973r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2973r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2973r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2973r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2973r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2973r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2974_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2973r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2974 :
    hubcapFit theRedpart rf8 p8_2973r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2974_1, c8_2974_2, c8_2974_3, c8_2974_4, c8_2974_5, c8_2974_6, c8_2974_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2973l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2973l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2973l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2973l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2975_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2973l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2975 :
    hubcapFit theRedpart rf8 p8_2973l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2975_1, c8_2975_2, c8_2975_3, c8_2975_4, c8_2975_5, c8_2975_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2972l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2972l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2972l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2977_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2972l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2977 :
    hubcapFit theRedpart rf8 p8_2972l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2977_1, c8_2977_2, c8_2977_3, c8_2977_4, c8_2977_5, c8_2977_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2979r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2979r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2979r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2979r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2979r) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2980_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2979r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2980 :
    hubcapFit theRedpart rf8 p8_2979r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2980_1, c8_2980_2, c8_2980_3, c8_2980_4, c8_2980_5, c8_2980_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2979l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2979l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2979l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2979l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2981_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2979l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2981 :
    hubcapFit theRedpart rf8 p8_2979l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2981_1, c8_2981_2, c8_2981_3, c8_2981_4, c8_2981_5, c8_2981_6, c8_2981_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2978l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2978l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2978l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2983_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2978l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2983 :
    hubcapFit theRedpart rf8 p8_2978l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2983_1, c8_2983_2, c8_2983_3, c8_2983_4, c8_2983_5, c8_2983_6, c8_2983_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2970l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2970l) (hubSubn 8 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2986_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2970l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2986 :
    hubcapFit theRedpart rf8 p8_2970l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2986_1, c8_2986_2, c8_2986_3, c8_2986_4, c8_2986_5, c8_2986_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2969l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2969l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2987_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2969l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2987 :
    hubcapFit theRedpart rf8 p8_2969l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2987_1, c8_2987_2, c8_2987_3, c8_2987_4, c8_2987_5, c8_2987_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2968l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2968l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2989_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2968l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2989 :
    hubcapFit theRedpart rf8 p8_2968l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2989_1, c8_2989_2, c8_2989_3, c8_2989_4, c8_2989_5, c8_2989_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2999r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2999r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2999r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2999r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2999r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2999r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2999r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3000_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2999r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3000 :
    hubcapFit theRedpart rf8 p8_2999r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3000_1, c8_3000_2, c8_3000_3, c8_3000_4, c8_3000_5, c8_3000_6, c8_3000_7, c8_3000_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2999l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2999l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2999l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3001_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2999l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3001 :
    hubcapFit theRedpart rf8 p8_2999l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3001_1, c8_3001_2, c8_3001_3, c8_3001_4, c8_3001_5, c8_3001_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2998l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2998l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3003_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2998l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3003 :
    hubcapFit theRedpart rf8 p8_2998l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3003_1, c8_3003_2, c8_3003_3, c8_3003_4, c8_3003_5, c8_3003_6, c8_3003_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2995l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2995l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2995l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2995l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3005_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2995l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3005 :
    hubcapFit theRedpart rf8 p8_2995l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3005_1, c8_3005_2, c8_3005_3, c8_3005_4, c8_3005_5, c8_3005_6, c8_3005_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3007_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3007_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3007_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2994l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3007_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2994l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3007_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2994l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3007 :
    hubcapFit theRedpart rf8 p8_2994l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3007_1, c8_3007_2, c8_3007_3, c8_3007_4, c8_3007_5]

end FourColor

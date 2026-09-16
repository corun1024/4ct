import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 67 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3136l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3136l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3136l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3136l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3168_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3168 :
    hubcapFit theRedpart rf9 p9_3136l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3168_1, c9_3168_2, c9_3168_3, c9_3168_4, c9_3168_5, c9_3168_6, c9_3168_7, c9_3168_8, c9_3168_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3188r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3188r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3188r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3189_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3188r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3189 :
    hubcapFit theRedpart rf9 p9_3188r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3189_1, c9_3189_2, c9_3189_3, c9_3189_4, c9_3189_5, c9_3189_6, c9_3189_7, c9_3189_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3188l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3188l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3188l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3188l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3190_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3188l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3190 :
    hubcapFit theRedpart rf9 p9_3188l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3190_1, c9_3190_2, c9_3190_3, c9_3190_4, c9_3190_5, c9_3190_6, c9_3190_7, c9_3190_8, c9_3190_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3187l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3187l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3187l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3192_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3192 :
    hubcapFit theRedpart rf9 p9_3187l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3192_1, c9_3192_2, c9_3192_3, c9_3192_4, c9_3192_5, c9_3192_6, c9_3192_7, c9_3192_8, c9_3192_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3186l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3186l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3194_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3194 :
    hubcapFit theRedpart rf9 p9_3186l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3194_1, c9_3194_2, c9_3194_3, c9_3194_4, c9_3194_5, c9_3194_6, c9_3194_7, c9_3194_8, c9_3194_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3185l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3185l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3185l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3185l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3185l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3196_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3185l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3196 :
    hubcapFit theRedpart rf9 p9_3185l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3196_1, c9_3196_2, c9_3196_3, c9_3196_4, c9_3196_5, c9_3196_6, c9_3196_7, c9_3196_8, c9_3196_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3183l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3183l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3183l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3183l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3183l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3198_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3183l) (hubSubn 9 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3198 :
    hubcapFit theRedpart rf9 p9_3183l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3198_1, c9_3198_2, c9_3198_3, c9_3198_4, c9_3198_5, c9_3198_6, c9_3198_7, c9_3198_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3181l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3181l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3200_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3181l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3200 :
    hubcapFit theRedpart rf9 p9_3181l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3200_1, c9_3200_2, c9_3200_3, c9_3200_4, c9_3200_5, c9_3200_6, c9_3200_7, c9_3200_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3180l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3180l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3180l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3202_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3180l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3202 :
    hubcapFit theRedpart rf9 p9_3180l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3202_1, c9_3202_2, c9_3202_3, c9_3202_4, c9_3202_5, c9_3202_6, c9_3202_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3178l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3178l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3178l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3204_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3178l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3204 :
    hubcapFit theRedpart rf9 p9_3178l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3204_1, c9_3204_2, c9_3204_3, c9_3204_4, c9_3204_5, c9_3204_6, c9_3204_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3212r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3212r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3212r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3212r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3212r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3212r) (hubSubn 9 7 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3213_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3212r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3213 :
    hubcapFit theRedpart rf9 p9_3212r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 9 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3213_1, c9_3213_2, c9_3213_3, c9_3213_4, c9_3213_5, c9_3213_6, c9_3213_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3212l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3212l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3212l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3212l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3212l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3212l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3212l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3214_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3212l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3214 :
    hubcapFit theRedpart rf9 p9_3212l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3214_1, c9_3214_2, c9_3214_3, c9_3214_4, c9_3214_5, c9_3214_6, c9_3214_7, c9_3214_8, c9_3214_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3211l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3211l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3211l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3211l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3216_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3216 :
    hubcapFit theRedpart rf9 p9_3211l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3216_1, c9_3216_2, c9_3216_3, c9_3216_4, c9_3216_5, c9_3216_6, c9_3216_7, c9_3216_8, c9_3216_9]

end FourColor

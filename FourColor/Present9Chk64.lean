import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 64 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3026l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3038_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3026l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3038 :
    hubcapFit theRedpart rf9 p9_3026l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3038_1, c9_3038_2, c9_3038_3, c9_3038_4, c9_3038_5, c9_3038_6, c9_3038_7, c9_3038_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3024l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3024l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3024l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3024l) (hubSubn 9 8 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3040_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3024l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3040 :
    hubcapFit theRedpart rf9 p9_3024l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 8 6 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3040_1, c9_3040_2, c9_3040_3, c9_3040_4, c9_3040_5, c9_3040_6, c9_3040_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3001l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3001l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3001l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3001l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3001l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3042_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3001l) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3042 :
    hubcapFit theRedpart rf9 p9_3001l
    (Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3042_1, c9_3042_2, c9_3042_3, c9_3042_4, c9_3042_5, c9_3042_6, c9_3042_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3000l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3000l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3044_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3000l) (hubSubn 9 8 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3044 :
    hubcapFit theRedpart rf9 p9_3000l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3044_1, c9_3044_2, c9_3044_3, c9_3044_4, c9_3044_5, c9_3044_6, c9_3044_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3046l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3046l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3047_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3046l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3047 :
    hubcapFit theRedpart rf9 p9_3046l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3047_1, c9_3047_2, c9_3047_3, c9_3047_4, c9_3047_5, c9_3047_6, c9_3047_7, c9_3047_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3046r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3046r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3046r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3046r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3046r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3046r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3046r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3049_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3046r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3049 :
    hubcapFit theRedpart rf9 p9_3046r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3049_1, c9_3049_2, c9_3049_3, c9_3049_4, c9_3049_5, c9_3049_6, c9_3049_7, c9_3049_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3066r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3066r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3066r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3067_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3066r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3067 :
    hubcapFit theRedpart rf9 p9_3066r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3067_1, c9_3067_2, c9_3067_3, c9_3067_4, c9_3067_5, c9_3067_6, c9_3067_7, c9_3067_8, c9_3067_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3066l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3066l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3068_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3066l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3068 :
    hubcapFit theRedpart rf9 p9_3066l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3068_1, c9_3068_2, c9_3068_3, c9_3068_4, c9_3068_5, c9_3068_6, c9_3068_7, c9_3068_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3064l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3064l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3070_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3064l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3070 :
    hubcapFit theRedpart rf9 p9_3064l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3070_1, c9_3070_2, c9_3070_3, c9_3070_4, c9_3070_5, c9_3070_6, c9_3070_7, c9_3070_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3063l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3063l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3063l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3072_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3063l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3072 :
    hubcapFit theRedpart rf9 p9_3063l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3072_1, c9_3072_2, c9_3072_3, c9_3072_4, c9_3072_5, c9_3072_6, c9_3072_7, c9_3072_8, c9_3072_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3062l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3062l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3062l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3062l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3062l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3062l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3062l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3074_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3062l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3074 :
    hubcapFit theRedpart rf9 p9_3062l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3074_1, c9_3074_2, c9_3074_3, c9_3074_4, c9_3074_5, c9_3074_6, c9_3074_7, c9_3074_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3082r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3082r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3082r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3082r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3082r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3082r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3082r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3082r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3083_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3082r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3083 :
    hubcapFit theRedpart rf9 p9_3082r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3083_1, c9_3083_2, c9_3083_3, c9_3083_4, c9_3083_5, c9_3083_6, c9_3083_7, c9_3083_8, c9_3083_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3082l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3082l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3082l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3082l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3082l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3082l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3082l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3082l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3084_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3082l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3084 :
    hubcapFit theRedpart rf9 p9_3082l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3084_1, c9_3084_2, c9_3084_3, c9_3084_4, c9_3084_5, c9_3084_6, c9_3084_7, c9_3084_8, c9_3084_9]

end FourColor

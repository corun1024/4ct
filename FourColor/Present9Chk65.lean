import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 65 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3079l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3079l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3079l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3086_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3086 :
    hubcapFit theRedpart rf9 p9_3079l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3086_1, c9_3086_2, c9_3086_3, c9_3086_4, c9_3086_5, c9_3086_6, c9_3086_7, c9_3086_8, c9_3086_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3078l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3078l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3078l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3078l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3078l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3088_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3078l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3088 :
    hubcapFit theRedpart rf9 p9_3078l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3088_1, c9_3088_2, c9_3088_3, c9_3088_4, c9_3088_5, c9_3088_6, c9_3088_7, c9_3088_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3076l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3076l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3076l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3076l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3076l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3076l) (hubSubn 9 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3090_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3076l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3090 :
    hubcapFit theRedpart rf9 p9_3076l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3090_1, c9_3090_2, c9_3090_3, c9_3090_4, c9_3090_5, c9_3090_6, c9_3090_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3058l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3058l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3058l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3058l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3058l) (hubSubn 9 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3058l) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3092_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3058l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3092 :
    hubcapFit theRedpart rf9 p9_3058l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3092_1, c9_3092_2, c9_3092_3, c9_3092_4, c9_3092_5, c9_3092_6, c9_3092_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3057l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3057l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3057l) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3094_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3057l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3094 :
    hubcapFit theRedpart rf9 p9_3057l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3094_1, c9_3094_2, c9_3094_3, c9_3094_4, c9_3094_5, c9_3094_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3056l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3056l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3056l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3056l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3056l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3056l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3095_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3056l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3095 :
    hubcapFit theRedpart rf9 p9_3056l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3095_1, c9_3095_2, c9_3095_3, c9_3095_4, c9_3095_5, c9_3095_6, c9_3095_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3055l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3055l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3055l) (hubSubn 9 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3097_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3055l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3097 :
    hubcapFit theRedpart rf9 p9_3055l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3097_1, c9_3097_2, c9_3097_3, c9_3097_4, c9_3097_5, c9_3097_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3098l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3098l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3098l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3098l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3098l) (hubSubn 9 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3099_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3098l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3099 :
    hubcapFit theRedpart rf9 p9_3098l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3099_1, c9_3099_2, c9_3099_3, c9_3099_4, c9_3099_5, c9_3099_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3098r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3098r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3098r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3098r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3098r) (hubSubn 9 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3101_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3098r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3101 :
    hubcapFit theRedpart rf9 p9_3098r
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3101_1, c9_3101_2, c9_3101_3, c9_3101_4, c9_3101_5, c9_3101_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3053l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3053l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3053l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3053l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3105_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3053l) (hubSubn 9 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3105 :
    hubcapFit theRedpart rf9 p9_3053l
    (Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3105_1, c9_3105_2, c9_3105_3, c9_3105_4, c9_3105_5, c9_3105_6, c9_3105_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3107l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3107l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3107l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3107l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3107l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3107l) (hubSubn 9 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3108_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3107l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3108 :
    hubcapFit theRedpart rf9 p9_3107l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3108_1, c9_3108_2, c9_3108_3, c9_3108_4, c9_3108_5, c9_3108_6, c9_3108_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3107r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3107r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3107r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3107r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3107r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3107r) (hubSubn 9 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3110_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3107r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3110 :
    hubcapFit theRedpart rf9 p9_3107r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3110_1, c9_3110_2, c9_3110_3, c9_3110_4, c9_3110_5, c9_3110_6, c9_3110_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2995l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2995l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2995l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3114_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2995l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3114 :
    hubcapFit theRedpart rf9 p9_2995l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3114_1, c9_3114_2, c9_3114_3, c9_3114_4, c9_3114_5, c9_3114_6, c9_3114_7, c9_3114_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2994l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2994l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2994l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2994l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3116_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3116 :
    hubcapFit theRedpart rf9 p9_2994l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3116_1, c9_3116_2, c9_3116_3, c9_3116_4, c9_3116_5, c9_3116_6, c9_3116_7, c9_3116_8, c9_3116_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3118l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3119_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3118l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3119 :
    hubcapFit theRedpart rf9 p9_3118l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3119_1, c9_3119_2, c9_3119_3, c9_3119_4, c9_3119_5, c9_3119_6, c9_3119_7, c9_3119_8]

end FourColor

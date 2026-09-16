import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 62 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3151l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3151l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3156_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3151l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3156 :
    hubcapFit theRedpart rf8 p8_3151l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3156_1, c8_3156_2, c8_3156_3, c8_3156_4, c8_3156_5, c8_3156_6, c8_3156_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3150l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3150l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3150l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3158_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3158 :
    hubcapFit theRedpart rf8 p8_3150l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3158_1, c8_3158_2, c8_3158_3, c8_3158_4, c8_3158_5, c8_3158_6, c8_3158_7, c8_3158_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3149l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3160_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3149l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3160 :
    hubcapFit theRedpart rf8 p8_3149l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3160_1, c8_3160_2, c8_3160_3, c8_3160_4, c8_3160_5, c8_3160_6, c8_3160_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3148l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3148l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3162_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3148l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3162 :
    hubcapFit theRedpart rf8 p8_3148l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3162_1, c8_3162_2, c8_3162_3, c8_3162_4, c8_3162_5, c8_3162_6, c8_3162_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3147l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3164_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3147l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3164 :
    hubcapFit theRedpart rf8 p8_3147l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3164_1, c8_3164_2, c8_3164_3, c8_3164_4, c8_3164_5, c8_3164_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3146l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3146l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3165_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3165 :
    hubcapFit theRedpart rf8 p8_3146l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3165_1, c8_3165_2, c8_3165_3, c8_3165_4, c8_3165_5, c8_3165_6, c8_3165_7, c8_3165_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3182r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3183_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3183 :
    hubcapFit theRedpart rf8 p8_3182r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3183_1, c8_3183_2, c8_3183_3, c8_3183_4, c8_3183_5, c8_3183_6, c8_3183_7, c8_3183_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3182l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3184_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3182l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3184 :
    hubcapFit theRedpart rf8 p8_3182l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3184_1, c8_3184_2, c8_3184_3, c8_3184_4, c8_3184_5, c8_3184_6, c8_3184_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3181l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3181l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3186_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3186 :
    hubcapFit theRedpart rf8 p8_3181l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3186_1, c8_3186_2, c8_3186_3, c8_3186_4, c8_3186_5, c8_3186_6, c8_3186_7, c8_3186_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3188_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3180l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3188 :
    hubcapFit theRedpart rf8 p8_3180l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3188_1, c8_3188_2, c8_3188_3, c8_3188_4, c8_3188_5, c8_3188_6, c8_3188_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3174l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3174l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3174l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3174l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3174l) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3191_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3174l) (hubSubn 8 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3191 :
    hubcapFit theRedpart rf8 p8_3174l
    (Hubcap.one 1 2 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 2 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3191_1, c8_3191_2, c8_3191_3, c8_3191_4, c8_3191_5, c8_3191_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3193_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3173l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3193_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3173l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3193_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3173l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3193_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3173l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3193_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3173l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3193 :
    hubcapFit theRedpart rf8 p8_3173l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3193_1, c8_3193_2, c8_3193_3, c8_3193_4, c8_3193_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3198r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3198r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3198r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3198r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3198r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3199_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3198r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3199 :
    hubcapFit theRedpart rf8 p8_3198r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3199_1, c8_3199_2, c8_3199_3, c8_3199_4, c8_3199_5, c8_3199_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3200_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3198l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3200_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3198l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3200_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3198l) (hubSubn 8 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3200_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3198l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3200_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3198l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3200 :
    hubcapFit theRedpart rf8 p8_3198l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 5 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3200_1, c8_3200_2, c8_3200_3, c8_3200_4, c8_3200_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3197l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3197l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3197l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3197l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3202_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3197l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3202 :
    hubcapFit theRedpart rf8 p8_3197l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3202_1, c8_3202_2, c8_3202_3, c8_3202_4, c8_3202_5, c8_3202_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3204_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3194l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3204_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3194l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3204_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3194l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3204_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3194l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3204_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3194l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3204 :
    hubcapFit theRedpart rf8 p8_3194l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3204_1, c8_3204_2, c8_3204_3, c8_3204_4, c8_3204_5]

end FourColor

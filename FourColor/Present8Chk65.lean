import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 65 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3296l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3296l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3296l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3296l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3296l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3296l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3296l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3305_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3296l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3305 :
    hubcapFit theRedpart rf8 p8_3296l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3305_1, c8_3305_2, c8_3305_3, c8_3305_4, c8_3305_5, c8_3305_6, c8_3305_7, c8_3305_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3294l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3294l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3294l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3294l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3294l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3294l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3307_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3294l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3307 :
    hubcapFit theRedpart rf8 p8_3294l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3307_1, c8_3307_2, c8_3307_3, c8_3307_4, c8_3307_5, c8_3307_6, c8_3307_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3293l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3293l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3293l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3309_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3293l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3309 :
    hubcapFit theRedpart rf8 p8_3293l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3309_1, c8_3309_2, c8_3309_3, c8_3309_4, c8_3309_5, c8_3309_6, c8_3309_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3291l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3291l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3311_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3291l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3311 :
    hubcapFit theRedpart rf8 p8_3291l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3311_1, c8_3311_2, c8_3311_3, c8_3311_4, c8_3311_5, c8_3311_6, c8_3311_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3290l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3290l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3290l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3290l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3290l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3313_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3290l) (hubSubn 8 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3313 :
    hubcapFit theRedpart rf8 p8_3290l
    (Hubcap.one 0 5 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3313_1, c8_3313_2, c8_3313_3, c8_3313_4, c8_3313_5, c8_3313_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3289l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3289l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3289l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3289l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3289l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3289l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3314_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3289l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3314 :
    hubcapFit theRedpart rf8 p8_3289l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3314_1, c8_3314_2, c8_3314_3, c8_3314_4, c8_3314_5, c8_3314_6, c8_3314_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3241l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3241l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3241l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3241l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3241l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3241l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3317_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3241l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3317 :
    hubcapFit theRedpart rf8 p8_3241l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3317_1, c8_3317_2, c8_3317_3, c8_3317_4, c8_3317_5, c8_3317_6, c8_3317_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3324r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3324r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3324r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3324r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3324r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3324r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3325_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3324r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3325 :
    hubcapFit theRedpart rf8 p8_3324r
    (Hubcap.one 0 5 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3325_1, c8_3325_2, c8_3325_3, c8_3325_4, c8_3325_5, c8_3325_6, c8_3325_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3324l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3324l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3324l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3324l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3324l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3326_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3324l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3326 :
    hubcapFit theRedpart rf8 p8_3324l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3326_1, c8_3326_2, c8_3326_3, c8_3326_4, c8_3326_5, c8_3326_6, c8_3326_7, c8_3326_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3333r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3333r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3333r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3333r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3333r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3333r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3334_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3333r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3334 :
    hubcapFit theRedpart rf8 p8_3333r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3334_1, c8_3334_2, c8_3334_3, c8_3334_4, c8_3334_5, c8_3334_6, c8_3334_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3333l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3335_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3333l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3335 :
    hubcapFit theRedpart rf8 p8_3333l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3335_1, c8_3335_2, c8_3335_3, c8_3335_4, c8_3335_5, c8_3335_6, c8_3335_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3332l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3337_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3332l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3337 :
    hubcapFit theRedpart rf8 p8_3332l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3337_1, c8_3337_2, c8_3337_3, c8_3337_4, c8_3337_5, c8_3337_6, c8_3337_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3331l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3331l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3339_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3331l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3339 :
    hubcapFit theRedpart rf8 p8_3331l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3339_1, c8_3339_2, c8_3339_3, c8_3339_4, c8_3339_5, c8_3339_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3330l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3330l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3330l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3330l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3330l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3340_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3330l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3340 :
    hubcapFit theRedpart rf8 p8_3330l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3340_1, c8_3340_2, c8_3340_3, c8_3340_4, c8_3340_5, c8_3340_6, c8_3340_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3329l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3329l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3329l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3329l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3329l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3342_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3329l) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3342 :
    hubcapFit theRedpart rf8 p8_3329l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3342_1, c8_3342_2, c8_3342_3, c8_3342_4, c8_3342_5, c8_3342_6, c8_3342_7]

end FourColor

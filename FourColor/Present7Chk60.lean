import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 60 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3237l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3237l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3237l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3237l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3242_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3237l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3242 :
    hubcapFit theRedpart rf7 p7_3237l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3242_1, c7_3242_2, c7_3242_3, c7_3242_4, c7_3242_5, c7_3242_6, c7_3242_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3234l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3234l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3234l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3234l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3244_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3244 :
    hubcapFit theRedpart rf7 p7_3234l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3244_1, c7_3244_2, c7_3244_3, c7_3244_4, c7_3244_5, c7_3244_6, c7_3244_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3250r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3250r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3250r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3250r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3250r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3250r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3251_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3250r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3251 :
    hubcapFit theRedpart rf7 p7_3250r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3251_1, c7_3251_2, c7_3251_3, c7_3251_4, c7_3251_5, c7_3251_6, c7_3251_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3250l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3250l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3250l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3250l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3250l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3252_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3252 :
    hubcapFit theRedpart rf7 p7_3250l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3252_1, c7_3252_2, c7_3252_3, c7_3252_4, c7_3252_5, c7_3252_6, c7_3252_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3249l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3249l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3254_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3254 :
    hubcapFit theRedpart rf7 p7_3249l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3254_1, c7_3254_2, c7_3254_3, c7_3254_4, c7_3254_5, c7_3254_6, c7_3254_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3246l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3246l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3256_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3256 :
    hubcapFit theRedpart rf7 p7_3246l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3256_1, c7_3256_2, c7_3256_3, c7_3256_4, c7_3256_5, c7_3256_6, c7_3256_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3232l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3232l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3232l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3232l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3232l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3232l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3258_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3232l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3258 :
    hubcapFit theRedpart rf7 p7_3232l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3258_1, c7_3258_2, c7_3258_3, c7_3258_4, c7_3258_5, c7_3258_6, c7_3258_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3273_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3273_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3273_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3272r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3273_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3272r) (hubSubn 7 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3273_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3272r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3273 :
    hubcapFit theRedpart rf7 p7_3272r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3273_1, c7_3273_2, c7_3273_3, c7_3273_4, c7_3273_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3274_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3272l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3274_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3274_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3272l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3274_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3272l) (hubSubn 7 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3274_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3272l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3274 :
    hubcapFit theRedpart rf7 p7_3272l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3274_1, c7_3274_2, c7_3274_3, c7_3274_4, c7_3274_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3276_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3276_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3271l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3276_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3276_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3271l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3276_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3271l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3276 :
    hubcapFit theRedpart rf7 p7_3271l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3276_1, c7_3276_2, c7_3276_3, c7_3276_4, c7_3276_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3277_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3277_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3270l) (hubSubn 7 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3277_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3270l) (hubSubn 7 5 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3277_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3270l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3277 :
    hubcapFit theRedpart rf7 p7_3270l
    (Hubcap.one 3 3 <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 2 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3277_1, c7_3277_2, c7_3277_3, c7_3277_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3279_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3279_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3279_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3269l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3279_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3269l) (hubSubn 7 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3279_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3269l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3279 :
    hubcapFit theRedpart rf7 p7_3269l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3279_1, c7_3279_2, c7_3279_3, c7_3279_4, c7_3279_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3288r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3288r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3288r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3288r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3288r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3289_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3288r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3289 :
    hubcapFit theRedpart rf7 p7_3288r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3289_1, c7_3289_2, c7_3289_3, c7_3289_4, c7_3289_5, c7_3289_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3288l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3288l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3290_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3290 :
    hubcapFit theRedpart rf7 p7_3288l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3290_1, c7_3290_2, c7_3290_3, c7_3290_4, c7_3290_5, c7_3290_6, c7_3290_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3287l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3287l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3287l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3287l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3287l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3287l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3292_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3287l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3292 :
    hubcapFit theRedpart rf7 p7_3287l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3292_1, c7_3292_2, c7_3292_3, c7_3292_4, c7_3292_5, c7_3292_6, c7_3292_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3286l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3294_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3286l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3294 :
    hubcapFit theRedpart rf7 p7_3286l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3294_1, c7_3294_2, c7_3294_3, c7_3294_4, c7_3294_5, c7_3294_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3284l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3284l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3284l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3284l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3296_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3284l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3296 :
    hubcapFit theRedpart rf7 p7_3284l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3296_1, c7_3296_2, c7_3296_3, c7_3296_4, c7_3296_5, c7_3296_6]

end FourColor

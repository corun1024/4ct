import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 69 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3246l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3246l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3257_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3246l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3257 :
    hubcapFit theRedpart rf9 p9_3246l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3257_1, c9_3257_2, c9_3257_3, c9_3257_4, c9_3257_5, c9_3257_6, c9_3257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3245l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3245l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3245l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3259_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3245l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3259 :
    hubcapFit theRedpart rf9 p9_3245l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3259_1, c9_3259_2, c9_3259_3, c9_3259_4, c9_3259_5, c9_3259_6, c9_3259_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3244l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3244l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3244l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3244l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3244l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3261_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3244l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3261 :
    hubcapFit theRedpart rf9 p9_3244l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3261_1, c9_3261_2, c9_3261_3, c9_3261_4, c9_3261_5, c9_3261_6, c9_3261_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3266l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3266l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3267_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3266l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3267 :
    hubcapFit theRedpart rf9 p9_3266l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3267_1, c9_3267_2, c9_3267_3, c9_3267_4, c9_3267_5, c9_3267_6, c9_3267_7, c9_3267_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3266r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3266r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3266r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3266r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3266r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3266r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3266r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3269_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3266r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3269 :
    hubcapFit theRedpart rf9 p9_3266r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3269_1, c9_3269_2, c9_3269_3, c9_3269_4, c9_3269_5, c9_3269_6, c9_3269_7, c9_3269_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3272l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3273_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3272l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3273 :
    hubcapFit theRedpart rf9 p9_3272l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3273_1, c9_3273_2, c9_3273_3, c9_3273_4, c9_3273_5, c9_3273_6, c9_3273_7, c9_3273_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3272r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3272r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3275_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3272r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3275 :
    hubcapFit theRedpart rf9 p9_3272r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3275_1, c9_3275_2, c9_3275_3, c9_3275_4, c9_3275_5, c9_3275_6, c9_3275_7, c9_3275_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3264r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3264r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3264r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3264r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3264r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3264r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3264r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3279_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3264r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3279 :
    hubcapFit theRedpart rf9 p9_3264r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3279_1, c9_3279_2, c9_3279_3, c9_3279_4, c9_3279_5, c9_3279_6, c9_3279_7, c9_3279_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3282l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3282l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3283_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3282l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3283 :
    hubcapFit theRedpart rf9 p9_3282l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3283_1, c9_3283_2, c9_3283_3, c9_3283_4, c9_3283_5, c9_3283_6, c9_3283_7, c9_3283_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3282r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3282r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3282r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3282r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3282r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3282r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3282r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3285_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3282r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3285 :
    hubcapFit theRedpart rf9 p9_3282r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3285_1, c9_3285_2, c9_3285_3, c9_3285_4, c9_3285_5, c9_3285_6, c9_3285_7, c9_3285_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3302r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3302r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3302r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3302r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3302r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3302r) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3303_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3302r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3303 :
    hubcapFit theRedpart rf9 p9_3302r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3303_1, c9_3303_2, c9_3303_3, c9_3303_4, c9_3303_5, c9_3303_6, c9_3303_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3302l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3302l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3302l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3302l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3304_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3304 :
    hubcapFit theRedpart rf9 p9_3302l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3304_1, c9_3304_2, c9_3304_3, c9_3304_4, c9_3304_5, c9_3304_6, c9_3304_7, c9_3304_8, c9_3304_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3299l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3299l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3299l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3299l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3299l) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3306_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3299l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3306 :
    hubcapFit theRedpart rf9 p9_3299l
    (Hubcap.one 3 5 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3306_1, c9_3306_2, c9_3306_3, c9_3306_4, c9_3306_5, c9_3306_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3298l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3298l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3298l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3298l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3298l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3298l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3308_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3298l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3308 :
    hubcapFit theRedpart rf9 p9_3298l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3308_1, c9_3308_2, c9_3308_3, c9_3308_4, c9_3308_5, c9_3308_6, c9_3308_7]

end FourColor

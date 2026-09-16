import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 61 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2727l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2727l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2727l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2727l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2727l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2727l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2727l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2894_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2727l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2894 :
    hubcapFit theRedpart rf9 p9_2727l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2894_1, c9_2894_2, c9_2894_3, c9_2894_4, c9_2894_5, c9_2894_6, c9_2894_7, c9_2894_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2899r) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2899r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2899r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2899r) (hubSubn 9 5 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2899r) (hubSubn 9 7 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2900_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2899r) (hubSubn 9 7 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2900 :
    hubcapFit theRedpart rf9 p9_2899r
    (Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.two 0 5 9 <|
     Hubcap.two 0 7 9 <|
     Hubcap.two 5 7 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2900_1, c9_2900_2, c9_2900_3, c9_2900_4, c9_2900_5, c9_2900_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2915r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2915r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2915r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2915r) (hubSubn 9 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2915r) (hubSubn 9 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2916_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2915r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2916 :
    hubcapFit theRedpart rf9 p9_2915r
    (Hubcap.one 1 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2916_1, c9_2916_2, c9_2916_3, c9_2916_4, c9_2916_5, c9_2916_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2915l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2915l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2915l) (hubSubn 9 5 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2915l) (hubSubn 9 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2917_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2915l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2917 :
    hubcapFit theRedpart rf9 p9_2915l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 8 <|
     Hubcap.two 2 6 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2917_1, c9_2917_2, c9_2917_3, c9_2917_4, c9_2917_5, c9_2917_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2920r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2920r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2920r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2920r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2920r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2920r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2920r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2921_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2920r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2921 :
    hubcapFit theRedpart rf9 p9_2920r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2921_1, c9_2921_2, c9_2921_3, c9_2921_4, c9_2921_5, c9_2921_6, c9_2921_7, c9_2921_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2920l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2920l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2920l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2920l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2920l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2922_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2922 :
    hubcapFit theRedpart rf9 p9_2920l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2922_1, c9_2922_2, c9_2922_3, c9_2922_4, c9_2922_5, c9_2922_6, c9_2922_7, c9_2922_8, c9_2922_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2919l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2919l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2924_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2924 :
    hubcapFit theRedpart rf9 p9_2919l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2924_1, c9_2924_2, c9_2924_3, c9_2924_4, c9_2924_5, c9_2924_6, c9_2924_7, c9_2924_8, c9_2924_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2913l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2926_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2926 :
    hubcapFit theRedpart rf9 p9_2913l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2926_1, c9_2926_2, c9_2926_3, c9_2926_4, c9_2926_5, c9_2926_6, c9_2926_7, c9_2926_8, c9_2926_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2912l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2912l) (hubSubn 9 5 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2928_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2912l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2928 :
    hubcapFit theRedpart rf9 p9_2912l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 8 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2928_1, c9_2928_2, c9_2928_3, c9_2928_4, c9_2928_5, c9_2928_6, c9_2928_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2930l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2930l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2930l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2930l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2931_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2930l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2931 :
    hubcapFit theRedpart rf9 p9_2930l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2931_1, c9_2931_2, c9_2931_3, c9_2931_4, c9_2931_5, c9_2931_6, c9_2931_7, c9_2931_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2930r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2930r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2930r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2930r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2930r) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2930r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2930r) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2933_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2930r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2933 :
    hubcapFit theRedpart rf9 p9_2930r
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2933_1, c9_2933_2, c9_2933_3, c9_2933_4, c9_2933_5, c9_2933_6, c9_2933_7, c9_2933_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2937r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2937r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2937r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2937r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2937r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2937r) (hubSubn 9 5 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2938_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2937r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2938 :
    hubcapFit theRedpart rf9 p9_2937r
    (Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 5 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2938_1, c9_2938_2, c9_2938_3, c9_2938_4, c9_2938_5, c9_2938_6, c9_2938_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2939l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2939l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2939l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2940_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2939l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2940 :
    hubcapFit theRedpart rf9 p9_2939l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2940_1, c9_2940_2, c9_2940_3, c9_2940_4, c9_2940_5, c9_2940_6, c9_2940_7, c9_2940_8, c9_2940_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2939r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2939r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2939r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2939r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2939r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2939r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2939r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2939r) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2942_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2939r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2942 :
    hubcapFit theRedpart rf9 p9_2939r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2942_1, c9_2942_2, c9_2942_3, c9_2942_4, c9_2942_5, c9_2942_6, c9_2942_7, c9_2942_8, c9_2942_9]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 61 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3283l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3297_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3283l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3297 :
    hubcapFit theRedpart rf7 p7_3283l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3297_1, c7_3297_2, c7_3297_3, c7_3297_4, c7_3297_5, c7_3297_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3282l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3299_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3282l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3299 :
    hubcapFit theRedpart rf7 p7_3282l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3299_1, c7_3299_2, c7_3299_3, c7_3299_4, c7_3299_5, c7_3299_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3281l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3300_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3281l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3300 :
    hubcapFit theRedpart rf7 p7_3281l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3300_1, c7_3300_2, c7_3300_3, c7_3300_4, c7_3300_5, c7_3300_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3302_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3302_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3302_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3302_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3280l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3302_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3280l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3302 :
    hubcapFit theRedpart rf7 p7_3280l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3302_1, c7_3302_2, c7_3302_3, c7_3302_4, c7_3302_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3304_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3304_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3266l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3304_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3266l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3304_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3266l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3304_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3266l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3304 :
    hubcapFit theRedpart rf7 p7_3266l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3304_1, c7_3304_2, c7_3304_3, c7_3304_4, c7_3304_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3265l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3265l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3265l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3306_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3265l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3306 :
    hubcapFit theRedpart rf7 p7_3265l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3306_1, c7_3306_2, c7_3306_3, c7_3306_4, c7_3306_5, c7_3306_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3312r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3312r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3312r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3312r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3312r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3313_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3312r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3313 :
    hubcapFit theRedpart rf7 p7_3312r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3313_1, c7_3313_2, c7_3313_3, c7_3313_4, c7_3313_5, c7_3313_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3314_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3312l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3314_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3314_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3312l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3314_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3312l) (hubSubn 7 6 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3314_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3312l) (hubSubn 7 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3314 :
    hubcapFit theRedpart rf7 p7_3312l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 6 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3314_1, c7_3314_2, c7_3314_3, c7_3314_4, c7_3314_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3316_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3311l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3316_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3311l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3316_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3311l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3316_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3311l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3316_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3311l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3316 :
    hubcapFit theRedpart rf7 p7_3311l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3316_1, c7_3316_2, c7_3316_3, c7_3316_4, c7_3316_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3310l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3310l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3310l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3310l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3310l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3317_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3310l) (hubSubn 7 6 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3317 :
    hubcapFit theRedpart rf7 p7_3310l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3317_1, c7_3317_2, c7_3317_3, c7_3317_4, c7_3317_5, c7_3317_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3319_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3319_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3308l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3319_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3308l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3319_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3308l) (hubSubn 7 6 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3319_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3308l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3319 :
    hubcapFit theRedpart rf7 p7_3308l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 6 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3319_1, c7_3319_2, c7_3319_3, c7_3319_4, c7_3319_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3326r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3326r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3326r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3326r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3326r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3327_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3326r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3327 :
    hubcapFit theRedpart rf7 p7_3326r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3327_1, c7_3327_2, c7_3327_3, c7_3327_4, c7_3327_5, c7_3327_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3326l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3326l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3326l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3326l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3328_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3326l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3328 :
    hubcapFit theRedpart rf7 p7_3326l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3328_1, c7_3328_2, c7_3328_3, c7_3328_4, c7_3328_5, c7_3328_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3325l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3325l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3325l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3330_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3325l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3330 :
    hubcapFit theRedpart rf7 p7_3325l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3330_1, c7_3330_2, c7_3330_3, c7_3330_4, c7_3330_5, c7_3330_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3331_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3324l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3331_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3324l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3331_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3324l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3331_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3324l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3331_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3324l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3331 :
    hubcapFit theRedpart rf7 p7_3324l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3331_1, c7_3331_2, c7_3331_3, c7_3331_4, c7_3331_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3335r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3335r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3335r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3335r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3335r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3336_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3335r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3336 :
    hubcapFit theRedpart rf7 p7_3335r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3336_1, c7_3336_2, c7_3336_3, c7_3336_4, c7_3336_5, c7_3336_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3337_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3337_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3337_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3337_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3335l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3337_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3335l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3337 :
    hubcapFit theRedpart rf7 p7_3335l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3337_1, c7_3337_2, c7_3337_3, c7_3337_4, c7_3337_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3339_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3334l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3339_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3339_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3339_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3334l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3339_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3334l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3339 :
    hubcapFit theRedpart rf7 p7_3334l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3339_1, c7_3339_2, c7_3339_3, c7_3339_4, c7_3339_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3333l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3333l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3340_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3333l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3340 :
    hubcapFit theRedpart rf7 p7_3333l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3340_1, c7_3340_2, c7_3340_3, c7_3340_4, c7_3340_5, c7_3340_6]

end FourColor

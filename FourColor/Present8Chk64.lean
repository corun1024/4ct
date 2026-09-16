import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 64 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3250l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3250l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3250l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3261_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3250l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3261 :
    hubcapFit theRedpart rf8 p8_3250l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3261_1, c8_3261_2, c8_3261_3, c8_3261_4, c8_3261_5, c8_3261_6, c8_3261_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3249l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3263_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3249l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3263 :
    hubcapFit theRedpart rf8 p8_3249l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3263_1, c8_3263_2, c8_3263_3, c8_3263_4, c8_3263_5, c8_3263_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3248l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3248l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3248l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3248l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3248l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3264_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3248l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3264 :
    hubcapFit theRedpart rf8 p8_3248l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3264_1, c8_3264_2, c8_3264_3, c8_3264_4, c8_3264_5, c8_3264_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3266_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3247l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3266_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3266_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3247l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3266_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3247l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3266_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3247l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3266 :
    hubcapFit theRedpart rf8 p8_3247l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3266_1, c8_3266_2, c8_3266_3, c8_3266_4, c8_3266_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3272r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3272r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3272r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3273_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3273 :
    hubcapFit theRedpart rf8 p8_3272r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3273_1, c8_3273_2, c8_3273_3, c8_3273_4, c8_3273_5, c8_3273_6, c8_3273_7, c8_3273_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3272l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3272l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3274_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3272l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3274 :
    hubcapFit theRedpart rf8 p8_3272l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3274_1, c8_3274_2, c8_3274_3, c8_3274_4, c8_3274_5, c8_3274_6, c8_3274_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3271l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3271l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3271l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3276_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3276 :
    hubcapFit theRedpart rf8 p8_3271l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3276_1, c8_3276_2, c8_3276_3, c8_3276_4, c8_3276_5, c8_3276_6, c8_3276_7, c8_3276_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3270l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3270l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3278_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3270l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3278 :
    hubcapFit theRedpart rf8 p8_3270l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3278_1, c8_3278_2, c8_3278_3, c8_3278_4, c8_3278_5, c8_3278_6, c8_3278_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3269l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3269l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3269l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3280_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3269l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3280 :
    hubcapFit theRedpart rf8 p8_3269l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3280_1, c8_3280_2, c8_3280_3, c8_3280_4, c8_3280_5, c8_3280_6, c8_3280_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3268l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3268l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3268l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3268l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3282_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3268l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3282 :
    hubcapFit theRedpart rf8 p8_3268l
    (Hubcap.one 0 5 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3282_1, c8_3282_2, c8_3282_3, c8_3282_4, c8_3282_5, c8_3282_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3284_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3244l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3284 :
    hubcapFit theRedpart rf8 p8_3244l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3284_1, c8_3284_2, c8_3284_3, c8_3284_4, c8_3284_5, c8_3284_6, c8_3284_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3286_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3243l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3286_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3243l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3286_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3243l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3286_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3243l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3286_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3243l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3286 :
    hubcapFit theRedpart rf8 p8_3243l
    (Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3286_1, c8_3286_2, c8_3286_3, c8_3286_4, c8_3286_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3299r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3299r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3299r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3299r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3299r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3299r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3299r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3300_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3299r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3300 :
    hubcapFit theRedpart rf8 p8_3299r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3300_1, c8_3300_2, c8_3300_3, c8_3300_4, c8_3300_5, c8_3300_6, c8_3300_7, c8_3300_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3299l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3299l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3299l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3301_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3299l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3301 :
    hubcapFit theRedpart rf8 p8_3299l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3301_1, c8_3301_2, c8_3301_3, c8_3301_4, c8_3301_5, c8_3301_6, c8_3301_7, c8_3301_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3297l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3297l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3297l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3297l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3303_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3297l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3303 :
    hubcapFit theRedpart rf8 p8_3297l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3303_1, c8_3303_2, c8_3303_3, c8_3303_4, c8_3303_5, c8_3303_6, c8_3303_7]

end FourColor

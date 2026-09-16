import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 16 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_669l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_669l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_734_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_734 :
    hubcapFit theRedpart rf10 p10_669l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_734_1, c10_734_2, c10_734_3, c10_734_4, c10_734_5, c10_734_6, c10_734_7, c10_734_8, c10_734_9, c10_734_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_668l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_668l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_736_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_668l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_736 :
    hubcapFit theRedpart rf10 p10_668l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_736_1, c10_736_2, c10_736_3, c10_736_4, c10_736_5, c10_736_6, c10_736_7, c10_736_8, c10_736_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_667l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_667l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_738_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_667l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_738 :
    hubcapFit theRedpart rf10 p10_667l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_738_1, c10_738_2, c10_738_3, c10_738_4, c10_738_5, c10_738_6, c10_738_7, c10_738_8, c10_738_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_666l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_666l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_666l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_666l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_740_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_740 :
    hubcapFit theRedpart rf10 p10_666l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_740_1, c10_740_2, c10_740_3, c10_740_4, c10_740_5, c10_740_6, c10_740_7, c10_740_8, c10_740_9, c10_740_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_768r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_768r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_768r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_768r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_768r) (hubSubn 10 2 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_768r) (hubSubn 10 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_769_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_768r) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_769 :
    hubcapFit theRedpart rf10 p10_768r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 8 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_769_1, c10_769_2, c10_769_3, c10_769_4, c10_769_5, c10_769_6, c10_769_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_768l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_768l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_768l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_768l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_770_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_770 :
    hubcapFit theRedpart rf10 p10_768l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_770_1, c10_770_2, c10_770_3, c10_770_4, c10_770_5, c10_770_6, c10_770_7, c10_770_8, c10_770_9, c10_770_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_766l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_766l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_773_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_766l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_773 :
    hubcapFit theRedpart rf10 p10_766l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_773_1, c10_773_2, c10_773_3, c10_773_4, c10_773_5, c10_773_6, c10_773_7, c10_773_8, c10_773_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_765l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_765l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_775_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_775 :
    hubcapFit theRedpart rf10 p10_765l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_775_1, c10_775_2, c10_775_3, c10_775_4, c10_775_5, c10_775_6, c10_775_7, c10_775_8, c10_775_9, c10_775_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_763l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_763l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_777_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_777 :
    hubcapFit theRedpart rf10 p10_763l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_777_1, c10_777_2, c10_777_3, c10_777_4, c10_777_5, c10_777_6, c10_777_7, c10_777_8, c10_777_9, c10_777_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_757l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_757l) (hubSubn 10 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_781_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_757l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_781 :
    hubcapFit theRedpart rf10 p10_757l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_781_1, c10_781_2, c10_781_3, c10_781_4, c10_781_5, c10_781_6, c10_781_7, c10_781_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_756l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_756l) (hubSubn 10 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_783_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_756l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_783 :
    hubcapFit theRedpart rf10 p10_756l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_783_1, c10_783_2, c10_783_3, c10_783_4, c10_783_5, c10_783_6, c10_783_7, c10_783_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_789r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_789r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_789r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_789r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_789r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_789r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_789r) (hubSubn 10 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_790_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_789r) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_790 :
    hubcapFit theRedpart rf10 p10_789r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_790_1, c10_790_2, c10_790_3, c10_790_4, c10_790_5, c10_790_6, c10_790_7, c10_790_8]

end FourColor

import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 18 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_821r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_821r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_821r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_822_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_821r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_822 :
    hubcapFit theRedpart rf10 p10_821r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_822_1, c10_822_2, c10_822_3, c10_822_4, c10_822_5, c10_822_6, c10_822_7, c10_822_8, c10_822_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_825l) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_825l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_826_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_825l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_826 :
    hubcapFit theRedpart rf10 p10_825l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_826_1, c10_826_2, c10_826_3, c10_826_4, c10_826_5, c10_826_6, c10_826_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_828l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_828l) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_828l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_829_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_828l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_829 :
    hubcapFit theRedpart rf10 p10_828l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_829_1, c10_829_2, c10_829_3, c10_829_4, c10_829_5, c10_829_6, c10_829_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_828r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_828r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_828r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_828r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_828r) (hubSubn 10 5 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_828r) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_831_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_828r) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_831 :
    hubcapFit theRedpart rf10 p10_828r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_831_1, c10_831_2, c10_831_3, c10_831_4, c10_831_5, c10_831_6, c10_831_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_824l) (hubSubn 10 5 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_835_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_824l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_835 :
    hubcapFit theRedpart rf10 p10_824l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_835_1, c10_835_2, c10_835_3, c10_835_4, c10_835_5, c10_835_6, c10_835_7, c10_835_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_859r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_859r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_859r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_860_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_859r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_860 :
    hubcapFit theRedpart rf10 p10_859r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_860_1, c10_860_2, c10_860_3, c10_860_4, c10_860_5, c10_860_6, c10_860_7, c10_860_8, c10_860_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_878r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_878r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_878r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_878r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_878r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_878r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_878r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_878r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_879_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_878r) (hubSubn 10 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_879 :
    hubcapFit theRedpart rf10 p10_878r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_879_1, c10_879_2, c10_879_3, c10_879_4, c10_879_5, c10_879_6, c10_879_7, c10_879_8, c10_879_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_878l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_878l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_878l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_880_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_878l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_880 :
    hubcapFit theRedpart rf10 p10_878l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 3 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_880_1, c10_880_2, c10_880_3, c10_880_4, c10_880_5, c10_880_6, c10_880_7, c10_880_8, c10_880_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_877l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_877l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_877l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_877l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_877l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_882_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_877l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_882 :
    hubcapFit theRedpart rf10 p10_877l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_882_1, c10_882_2, c10_882_3, c10_882_4, c10_882_5, c10_882_6, c10_882_7, c10_882_8, c10_882_9, c10_882_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_876l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_876l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_876l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_876l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_876l) (hubSubn 10 9 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_884_10 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_876l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_884 :
    hubcapFit theRedpart rf10 p10_876l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.two 7 9 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_884_1, c10_884_2, c10_884_3, c10_884_4, c10_884_5, c10_884_6, c10_884_7, c10_884_8, c10_884_9, c10_884_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_875l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_875l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_875l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_886_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_886 :
    hubcapFit theRedpart rf10 p10_875l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_886_1, c10_886_2, c10_886_3, c10_886_4, c10_886_5, c10_886_6, c10_886_7, c10_886_8, c10_886_9, c10_886_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_873l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_873l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_889_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_889 :
    hubcapFit theRedpart rf10 p10_873l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_889_1, c10_889_2, c10_889_3, c10_889_4, c10_889_5, c10_889_6, c10_889_7, c10_889_8, c10_889_9, c10_889_10]

end FourColor

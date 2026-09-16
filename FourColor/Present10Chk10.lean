import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 10 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_468l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_491_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_468l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_491 :
    hubcapFit theRedpart rf10 p10_468l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_491_1, c10_491_2, c10_491_3, c10_491_4, c10_491_5, c10_491_6, c10_491_7, c10_491_8, c10_491_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_467l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_467l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_467l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_493_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_467l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_493 :
    hubcapFit theRedpart rf10 p10_467l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_493_1, c10_493_2, c10_493_3, c10_493_4, c10_493_5, c10_493_6, c10_493_7, c10_493_8, c10_493_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_495l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_495l) (hubSubn 10 6 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_496_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_495l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_496 :
    hubcapFit theRedpart rf10 p10_495l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_496_1, c10_496_2, c10_496_3, c10_496_4, c10_496_5, c10_496_6, c10_496_7, c10_496_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_498l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_498l) (hubSubn 10 6 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_499_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_498l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_499 :
    hubcapFit theRedpart rf10 p10_498l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_499_1, c10_499_2, c10_499_3, c10_499_4, c10_499_5, c10_499_6, c10_499_7, c10_499_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_498r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_498r) (hubSubn 10 6 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_501_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_498r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_501 :
    hubcapFit theRedpart rf10 p10_498r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_501_1, c10_501_2, c10_501_3, c10_501_4, c10_501_5, c10_501_6, c10_501_7, c10_501_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_506r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_506r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_506r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_506r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_506r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_506r) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_506r) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_506r) (hubSubn 10 9 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_507_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_506r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_507 :
    hubcapFit theRedpart rf10 p10_506r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 7 8 7 <|
     Hubcap.two 7 9 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_507_1, c10_507_2, c10_507_3, c10_507_4, c10_507_5, c10_507_6, c10_507_7, c10_507_8, c10_507_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_506l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_506l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_506l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_508_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_506l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_508 :
    hubcapFit theRedpart rf10 p10_506l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_508_1, c10_508_2, c10_508_3, c10_508_4, c10_508_5, c10_508_6, c10_508_7, c10_508_8, c10_508_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_505l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_505l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_510_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_505l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_510 :
    hubcapFit theRedpart rf10 p10_505l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_510_1, c10_510_2, c10_510_3, c10_510_4, c10_510_5, c10_510_6, c10_510_7, c10_510_8, c10_510_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_464l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_464l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_464l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_464l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_464l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_512_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_464l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_512 :
    hubcapFit theRedpart rf10 p10_464l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_512_1, c10_512_2, c10_512_3, c10_512_4, c10_512_5, c10_512_6, c10_512_7, c10_512_8, c10_512_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_514r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_514r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_514r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_514r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_514r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_514r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_514r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_514r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_515_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_514r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_515 :
    hubcapFit theRedpart rf10 p10_514r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_515_1, c10_515_2, c10_515_3, c10_515_4, c10_515_5, c10_515_6, c10_515_7, c10_515_8, c10_515_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_514l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_514l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_514l) (hubSubn 10 3 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_516_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_514l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_516 :
    hubcapFit theRedpart rf10 p10_514l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_516_1, c10_516_2, c10_516_3, c10_516_4, c10_516_5, c10_516_6, c10_516_7, c10_516_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_462l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_518_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_462l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_518 :
    hubcapFit theRedpart rf10 p10_462l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_518_1, c10_518_2, c10_518_3, c10_518_4, c10_518_5, c10_518_6, c10_518_7, c10_518_8, c10_518_9, c10_518_10]

end FourColor

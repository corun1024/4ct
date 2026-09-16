import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 73 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3691l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3691l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3691l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3691l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3691l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3691l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3696_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3691l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3696 :
    hubcapFit theRedpart rf8 p8_3691l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3696_1, c8_3696_2, c8_3696_3, c8_3696_4, c8_3696_5, c8_3696_6, c8_3696_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3690l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3690l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3690l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3690l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3690l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3698_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3690l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3698 :
    hubcapFit theRedpart rf8 p8_3690l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3698_1, c8_3698_2, c8_3698_3, c8_3698_4, c8_3698_5, c8_3698_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3704_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3703r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3704_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3703r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3704_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3703r) (hubSubn 8 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3704_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3703r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3704_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3703r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3704 :
    hubcapFit theRedpart rf8 p8_3703r
    (Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3704_1, c8_3704_2, c8_3704_3, c8_3704_4, c8_3704_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3703l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3703l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3703l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3703l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3705_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3703l) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3705 :
    hubcapFit theRedpart rf8 p8_3703l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3705_1, c8_3705_2, c8_3705_3, c8_3705_4, c8_3705_5, c8_3705_6, c8_3705_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3707_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3707_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3707_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3702l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3707_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3702l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3707_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3702l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3707 :
    hubcapFit theRedpart rf8 p8_3702l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3707_1, c8_3707_2, c8_3707_3, c8_3707_4, c8_3707_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3701l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3701l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3708_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3701l) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3708 :
    hubcapFit theRedpart rf8 p8_3701l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3708_1, c8_3708_2, c8_3708_3, c8_3708_4, c8_3708_5, c8_3708_6, c8_3708_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3700l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3700l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3700l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3700l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3710_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3700l) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3710 :
    hubcapFit theRedpart rf8 p8_3700l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3710_1, c8_3710_2, c8_3710_3, c8_3710_4, c8_3710_5, c8_3710_6, c8_3710_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3722r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3722r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3722r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3722r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3722r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3722r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3722r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3723_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3722r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3723 :
    hubcapFit theRedpart rf8 p8_3722r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3723_1, c8_3723_2, c8_3723_3, c8_3723_4, c8_3723_5, c8_3723_6, c8_3723_7, c8_3723_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3722l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3722l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3722l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3722l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3724_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3722l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3724 :
    hubcapFit theRedpart rf8 p8_3722l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3724_1, c8_3724_2, c8_3724_3, c8_3724_4, c8_3724_5, c8_3724_6, c8_3724_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3721l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3721l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3721l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3721l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3721l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3726_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3721l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3726 :
    hubcapFit theRedpart rf8 p8_3721l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3726_1, c8_3726_2, c8_3726_3, c8_3726_4, c8_3726_5, c8_3726_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3718l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3718l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3718l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3718l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3718l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3728_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3718l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3728 :
    hubcapFit theRedpart rf8 p8_3718l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3728_1, c8_3728_2, c8_3728_3, c8_3728_4, c8_3728_5, c8_3728_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3730_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3717l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3730_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3717l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3730_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3717l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3730_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3717l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3730_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3717l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3730 :
    hubcapFit theRedpart rf8 p8_3717l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3730_1, c8_3730_2, c8_3730_3, c8_3730_4, c8_3730_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3716l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3716l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3716l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3731_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3716l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3731 :
    hubcapFit theRedpart rf8 p8_3716l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3731_1, c8_3731_2, c8_3731_3, c8_3731_4, c8_3731_5, c8_3731_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3715l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3715l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3733_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3715l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3733 :
    hubcapFit theRedpart rf8 p8_3715l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3733_1, c8_3733_2, c8_3733_3, c8_3733_4, c8_3733_5, c8_3733_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3745r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3745r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3745r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3745r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3745r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3745r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3745r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3746_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3745r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3746 :
    hubcapFit theRedpart rf8 p8_3745r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3746_1, c8_3746_2, c8_3746_3, c8_3746_4, c8_3746_5, c8_3746_6, c8_3746_7, c8_3746_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3745l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3745l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3745l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3747_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3745l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3747 :
    hubcapFit theRedpart rf8 p8_3745l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3747_1, c8_3747_2, c8_3747_3, c8_3747_4, c8_3747_5, c8_3747_6, c8_3747_7]

end FourColor

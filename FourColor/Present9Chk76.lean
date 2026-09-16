import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 76 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3607r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3607r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3607r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3607r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3607r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3607r) (hubSubn 9 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3608_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3607r) (hubSubn 9 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3608 :
    hubcapFit theRedpart rf9 p9_3607r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3608_1, c9_3608_2, c9_3608_3, c9_3608_4, c9_3608_5, c9_3608_6, c9_3608_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3607l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3607l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3607l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3607l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3607l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3607l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3607l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3609_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3607l) (hubSubn 9 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3609 :
    hubcapFit theRedpart rf9 p9_3607l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3609_1, c9_3609_2, c9_3609_3, c9_3609_4, c9_3609_5, c9_3609_6, c9_3609_7, c9_3609_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3605l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3605l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3605l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3605l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3605l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3605l) (hubSubn 9 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3611_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3605l) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3611 :
    hubcapFit theRedpart rf9 p9_3605l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3611_1, c9_3611_2, c9_3611_3, c9_3611_4, c9_3611_5, c9_3611_6, c9_3611_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3604l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3604l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3604l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3604l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3604l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3604l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3613_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3604l) (hubSubn 9 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3613 :
    hubcapFit theRedpart rf9 p9_3604l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3613_1, c9_3613_2, c9_3613_3, c9_3613_4, c9_3613_5, c9_3613_6, c9_3613_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3603l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3603l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3603l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3603l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3603l) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3615_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3603l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3615 :
    hubcapFit theRedpart rf9 p9_3603l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3615_1, c9_3615_2, c9_3615_3, c9_3615_4, c9_3615_5, c9_3615_6, c9_3615_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3602l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3602l) (hubSubn 9 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3617_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3602l) (hubSubn 9 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3617 :
    hubcapFit theRedpart rf9 p9_3602l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3617_1, c9_3617_2, c9_3617_3, c9_3617_4, c9_3617_5, c9_3617_6, c9_3617_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3601l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3601l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3601l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3601l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3601l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3601l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3619_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3619 :
    hubcapFit theRedpart rf9 p9_3601l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3619_1, c9_3619_2, c9_3619_3, c9_3619_4, c9_3619_5, c9_3619_6, c9_3619_7, c9_3619_8, c9_3619_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3600l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3600l) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3621_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3600l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3621 :
    hubcapFit theRedpart rf9 p9_3600l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3621_1, c9_3621_2, c9_3621_3, c9_3621_4, c9_3621_5, c9_3621_6, c9_3621_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3599l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3599l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3599l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3599l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3599l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3599l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3599l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3623_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3599l) (hubSubn 9 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3623 :
    hubcapFit theRedpart rf9 p9_3599l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3623_1, c9_3623_2, c9_3623_3, c9_3623_4, c9_3623_5, c9_3623_6, c9_3623_7, c9_3623_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3626r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3626r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3626r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3626r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3626r) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3627_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3626r) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3627 :
    hubcapFit theRedpart rf9 p9_3626r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3627_1, c9_3627_2, c9_3627_3, c9_3627_4, c9_3627_5, c9_3627_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3626l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3626l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3626l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3626l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3626l) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3628_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3626l) (hubSubn 9 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3628 :
    hubcapFit theRedpart rf9 p9_3626l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3628_1, c9_3628_2, c9_3628_3, c9_3628_4, c9_3628_5, c9_3628_6, c9_3628_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3597l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3597l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3630_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3597l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3630 :
    hubcapFit theRedpart rf9 p9_3597l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3630_1, c9_3630_2, c9_3630_3, c9_3630_4, c9_3630_5, c9_3630_6, c9_3630_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3547l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3547l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3547l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3547l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3547l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3547l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3633_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3547l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3633 :
    hubcapFit theRedpart rf9 p9_3547l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3633_1, c9_3633_2, c9_3633_3, c9_3633_4, c9_3633_5, c9_3633_6, c9_3633_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3546l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3546l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3546l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3546l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3546l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3635_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3546l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3635 :
    hubcapFit theRedpart rf9 p9_3546l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3635_1, c9_3635_2, c9_3635_3, c9_3635_4, c9_3635_5, c9_3635_6, c9_3635_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3650r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3650r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3650r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3650r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3650r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3650r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3650r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3651_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3650r) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3651 :
    hubcapFit theRedpart rf9 p9_3650r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3651_1, c9_3651_2, c9_3651_3, c9_3651_4, c9_3651_5, c9_3651_6, c9_3651_7, c9_3651_8]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 67 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3615l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3620_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3615l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3620 :
    hubcapFit theRedpart rf7 p7_3615l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3620_1, c7_3620_2, c7_3620_3, c7_3620_4, c7_3620_5, c7_3620_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3614l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3614l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3614l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3621_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3614l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3621 :
    hubcapFit theRedpart rf7 p7_3614l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3621_1, c7_3621_2, c7_3621_3, c7_3621_4, c7_3621_5, c7_3621_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3613l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3613l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3613l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3623_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3613l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3623 :
    hubcapFit theRedpart rf7 p7_3613l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3623_1, c7_3623_2, c7_3623_3, c7_3623_4, c7_3623_5, c7_3623_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3628r) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3628r) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3628r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3628r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3629_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3628r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3629 :
    hubcapFit theRedpart rf7 p7_3628r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3629_1, c7_3629_2, c7_3629_3, c7_3629_4, c7_3629_5, c7_3629_6, c7_3629_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3641r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3641r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3641r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3641r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3641r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3642_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3641r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3642 :
    hubcapFit theRedpart rf7 p7_3641r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3642_1, c7_3642_2, c7_3642_3, c7_3642_4, c7_3642_5, c7_3642_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3641l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3641l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3643_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3641l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3643 :
    hubcapFit theRedpart rf7 p7_3641l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3643_1, c7_3643_2, c7_3643_3, c7_3643_4, c7_3643_5, c7_3643_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3640l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3640l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3640l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3645_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3645 :
    hubcapFit theRedpart rf7 p7_3640l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3645_1, c7_3645_2, c7_3645_3, c7_3645_4, c7_3645_5, c7_3645_6, c7_3645_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3647_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3639l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3647_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3639l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3647_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3639l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3647_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3639l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3647_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3639l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3647 :
    hubcapFit theRedpart rf7 p7_3639l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3647_1, c7_3647_2, c7_3647_3, c7_3647_4, c7_3647_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3648_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3638l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3648_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3638l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3648_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3638l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3648_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3638l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3648_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3638l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3648 :
    hubcapFit theRedpart rf7 p7_3638l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3648_1, c7_3648_2, c7_3648_3, c7_3648_4, c7_3648_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3650_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3636l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3650_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3636l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3650_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3636l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3650_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3636l) (hubSubn 7 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3650_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3636l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3650 :
    hubcapFit theRedpart rf7 p7_3636l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3650_1, c7_3650_2, c7_3650_3, c7_3650_4, c7_3650_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3634l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3634l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3634l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3634l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3634l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3652_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3634l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3652 :
    hubcapFit theRedpart rf7 p7_3634l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3652_1, c7_3652_2, c7_3652_3, c7_3652_4, c7_3652_5, c7_3652_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3654_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3633l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3654_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3633l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3654_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3633l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3654_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3633l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3654_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3633l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3654 :
    hubcapFit theRedpart rf7 p7_3633l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3654_1, c7_3654_2, c7_3654_3, c7_3654_4, c7_3654_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3656_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3656_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3631l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3656_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3631l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3656_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3631l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3656_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3631l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3656 :
    hubcapFit theRedpart rf7 p7_3631l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 (-2) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3656_1, c7_3656_2, c7_3656_3, c7_3656_4, c7_3656_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3658_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3658_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3626l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3658_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3626l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3658_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3626l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3658_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3626l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3658 :
    hubcapFit theRedpart rf7 p7_3626l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3658_1, c7_3658_2, c7_3658_3, c7_3658_4, c7_3658_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3673r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3673r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3673r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3673r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3673r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3673r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3674_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3673r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3674 :
    hubcapFit theRedpart rf7 p7_3673r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3674_1, c7_3674_2, c7_3674_3, c7_3674_4, c7_3674_5, c7_3674_6, c7_3674_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3673l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3673l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3673l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3673l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3673l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3675_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3673l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3675 :
    hubcapFit theRedpart rf7 p7_3673l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3675_1, c7_3675_2, c7_3675_3, c7_3675_4, c7_3675_5, c7_3675_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3671l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3671l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3677_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3671l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3677 :
    hubcapFit theRedpart rf7 p7_3671l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3677_1, c7_3677_2, c7_3677_3, c7_3677_4, c7_3677_5, c7_3677_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3670l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3670l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3670l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3670l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3670l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3679_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3670l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3679 :
    hubcapFit theRedpart rf7 p7_3670l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3679_1, c7_3679_2, c7_3679_3, c7_3679_4, c7_3679_5, c7_3679_6]

end FourColor

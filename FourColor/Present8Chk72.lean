import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 72 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3640l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3640l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3656_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3640l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3656 :
    hubcapFit theRedpart rf8 p8_3640l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3656_1, c8_3656_2, c8_3656_3, c8_3656_4, c8_3656_5, c8_3656_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3658_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3639l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3658_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3639l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3658_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3639l) (hubSubn 8 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3658_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3639l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3658_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3639l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3658 :
    hubcapFit theRedpart rf8 p8_3639l
    (Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3658_1, c8_3658_2, c8_3658_3, c8_3658_4, c8_3658_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3638l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3638l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3638l) (hubSubn 8 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3659_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3638l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3659 :
    hubcapFit theRedpart rf8 p8_3638l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3659_1, c8_3659_2, c8_3659_3, c8_3659_4, c8_3659_5, c8_3659_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3668r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3668r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3668r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3668r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3668r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3668r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3669_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3668r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3669 :
    hubcapFit theRedpart rf8 p8_3668r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3669_1, c8_3669_2, c8_3669_3, c8_3669_4, c8_3669_5, c8_3669_6, c8_3669_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3668l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3670_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3668l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3670 :
    hubcapFit theRedpart rf8 p8_3668l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3670_1, c8_3670_2, c8_3670_3, c8_3670_4, c8_3670_5, c8_3670_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3667l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3672_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3667l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3672 :
    hubcapFit theRedpart rf8 p8_3667l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3672_1, c8_3672_2, c8_3672_3, c8_3672_4, c8_3672_5, c8_3672_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3666l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3673_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3666l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3673 :
    hubcapFit theRedpart rf8 p8_3666l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3673_1, c8_3673_2, c8_3673_3, c8_3673_4, c8_3673_5, c8_3673_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3665l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3675_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3665l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3675 :
    hubcapFit theRedpart rf8 p8_3665l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3675_1, c8_3675_2, c8_3675_3, c8_3675_4, c8_3675_5, c8_3675_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3664l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3676_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3664l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3676 :
    hubcapFit theRedpart rf8 p8_3664l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3676_1, c8_3676_2, c8_3676_3, c8_3676_4, c8_3676_5, c8_3676_6, c8_3676_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3663l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3678_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3663l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3678 :
    hubcapFit theRedpart rf8 p8_3663l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3678_1, c8_3678_2, c8_3678_3, c8_3678_4, c8_3678_5, c8_3678_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3662l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3662l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3662l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3662l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3679_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3662l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3679 :
    hubcapFit theRedpart rf8 p8_3662l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3679_1, c8_3679_2, c8_3679_3, c8_3679_4, c8_3679_5, c8_3679_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3681_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3661l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3681 :
    hubcapFit theRedpart rf8 p8_3661l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3681_1, c8_3681_2, c8_3681_3, c8_3681_4, c8_3681_5, c8_3681_6, c8_3681_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3683_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3635l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3683_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3635l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3683_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3635l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3683_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3635l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3683_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3635l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3683 :
    hubcapFit theRedpart rf8 p8_3635l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3683_1, c8_3683_2, c8_3683_3, c8_3683_4, c8_3683_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3686r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3686r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3686r) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3686r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3686r) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3687_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3686r) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3687 :
    hubcapFit theRedpart rf8 p8_3686r
    (Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3687_1, c8_3687_2, c8_3687_3, c8_3687_4, c8_3687_5, c8_3687_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3686l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3686l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3686l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3686l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3688_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3686l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3688 :
    hubcapFit theRedpart rf8 p8_3686l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3688_1, c8_3688_2, c8_3688_3, c8_3688_4, c8_3688_5, c8_3688_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3693_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3692r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3693_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3692r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3693_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3692r) (hubSubn 8 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3693_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3692r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3693_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3692r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3693 :
    hubcapFit theRedpart rf8 p8_3692r
    (Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3693_1, c8_3693_2, c8_3693_3, c8_3693_4, c8_3693_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3692l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3692l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3692l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3694_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3692l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3694 :
    hubcapFit theRedpart rf8 p8_3692l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3694_1, c8_3694_2, c8_3694_3, c8_3694_4, c8_3694_5, c8_3694_6]

end FourColor

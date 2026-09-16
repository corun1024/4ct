import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 77 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3650l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3650l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3650l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3650l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3650l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3650l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3650l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3650l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3652_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3650l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3652 :
    hubcapFit theRedpart rf9 p9_3650l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3652_1, c9_3652_2, c9_3652_3, c9_3652_4, c9_3652_5, c9_3652_6, c9_3652_7, c9_3652_8, c9_3652_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3649l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3649l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3654_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3649l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3654 :
    hubcapFit theRedpart rf9 p9_3649l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3654_1, c9_3654_2, c9_3654_3, c9_3654_4, c9_3654_5, c9_3654_6, c9_3654_7, c9_3654_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3648l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3648l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3648l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3648l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3648l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3648l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3648l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3656_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3648l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3656 :
    hubcapFit theRedpart rf9 p9_3648l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3656_1, c9_3656_2, c9_3656_3, c9_3656_4, c9_3656_5, c9_3656_6, c9_3656_7, c9_3656_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3647l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3647l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3647l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3647l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3647l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3647l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3647l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3658_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3658 :
    hubcapFit theRedpart rf9 p9_3647l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3658_1, c9_3658_2, c9_3658_3, c9_3658_4, c9_3658_5, c9_3658_6, c9_3658_7, c9_3658_8, c9_3658_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3644l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3644l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3644l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3644l) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3660_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3644l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3660 :
    hubcapFit theRedpart rf9 p9_3644l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3660_1, c9_3660_2, c9_3660_3, c9_3660_4, c9_3660_5, c9_3660_6, c9_3660_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3665r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3665r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3665r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3665r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3665r) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3666_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3665r) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3666 :
    hubcapFit theRedpart rf9 p9_3665r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3666_1, c9_3666_2, c9_3666_3, c9_3666_4, c9_3666_5, c9_3666_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3665l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3665l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3665l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3665l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3665l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3667_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3665l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3667 :
    hubcapFit theRedpart rf9 p9_3665l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3667_1, c9_3667_2, c9_3667_3, c9_3667_4, c9_3667_5, c9_3667_6, c9_3667_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3664l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3664l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3664l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3664l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3664l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3669_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3664l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3669 :
    hubcapFit theRedpart rf9 p9_3664l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3669_1, c9_3669_2, c9_3669_3, c9_3669_4, c9_3669_5, c9_3669_6, c9_3669_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3663l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3663l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3663l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3663l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3671_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3663l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3671 :
    hubcapFit theRedpart rf9 p9_3663l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3671_1, c9_3671_2, c9_3671_3, c9_3671_4, c9_3671_5, c9_3671_6, c9_3671_7, c9_3671_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3638l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3638l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3638l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3638l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3673_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3638l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3673 :
    hubcapFit theRedpart rf9 p9_3638l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3673_1, c9_3673_2, c9_3673_3, c9_3673_4, c9_3673_5, c9_3673_6, c9_3673_7, c9_3673_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3543l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3675_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3543l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3675 :
    hubcapFit theRedpart rf9 p9_3543l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3675_1, c9_3675_2, c9_3675_3, c9_3675_4, c9_3675_5, c9_3675_6, c9_3675_7, c9_3675_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3542l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3677_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3542l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3677 :
    hubcapFit theRedpart rf9 p9_3542l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3677_1, c9_3677_2, c9_3677_3, c9_3677_4, c9_3677_5, c9_3677_6, c9_3677_7, c9_3677_8]

end FourColor

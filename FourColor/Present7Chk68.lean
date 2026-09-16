import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 68 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3669l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3669l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3669l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3680_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3669l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3680 :
    hubcapFit theRedpart rf7 p7_3669l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3680_1, c7_3680_2, c7_3680_3, c7_3680_4, c7_3680_5, c7_3680_6, c7_3680_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3682_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3682_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3682_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3667l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3682_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3667l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3682_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3667l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3682 :
    hubcapFit theRedpart rf7 p7_3667l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3682_1, c7_3682_2, c7_3682_3, c7_3682_4, c7_3682_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3666l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3666l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3684_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3666l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3684 :
    hubcapFit theRedpart rf7 p7_3666l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3684_1, c7_3684_2, c7_3684_3, c7_3684_4, c7_3684_5, c7_3684_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3665l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3685_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3665l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3685 :
    hubcapFit theRedpart rf7 p7_3665l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3685_1, c7_3685_2, c7_3685_3, c7_3685_4, c7_3685_5, c7_3685_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3687_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3687_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3687_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3664l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3687_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3664l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3687_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3664l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3687 :
    hubcapFit theRedpart rf7 p7_3664l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3687_1, c7_3687_2, c7_3687_3, c7_3687_4, c7_3687_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3688_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3688_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3688_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3663l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3688_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3663l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3688_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3663l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3688 :
    hubcapFit theRedpart rf7 p7_3663l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3688_1, c7_3688_2, c7_3688_3, c7_3688_4, c7_3688_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3662l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3662l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3690_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3662l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3690 :
    hubcapFit theRedpart rf7 p7_3662l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3690_1, c7_3690_2, c7_3690_3, c7_3690_4, c7_3690_5, c7_3690_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3661l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3661l) (hubSubn 7 4 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3661l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3691_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3661l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3691 :
    hubcapFit theRedpart rf7 p7_3661l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 4 2 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3691_1, c7_3691_2, c7_3691_3, c7_3691_4, c7_3691_5, c7_3691_6, c7_3691_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3660l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3660l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3660l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3660l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3693_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3660l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3693 :
    hubcapFit theRedpart rf7 p7_3660l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3693_1, c7_3693_2, c7_3693_3, c7_3693_4, c7_3693_5, c7_3693_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3696l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3696l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3697_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3696l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3697 :
    hubcapFit theRedpart rf7 p7_3696l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3697_1, c7_3697_2, c7_3697_3, c7_3697_4, c7_3697_5, c7_3697_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3696r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3696r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3699_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3696r) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3699 :
    hubcapFit theRedpart rf7 p7_3696r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3699_1, c7_3699_2, c7_3699_3, c7_3699_4, c7_3699_5, c7_3699_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3709_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3708r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3709_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3708r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3709_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3708r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3709_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3708r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3709_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3708r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3709 :
    hubcapFit theRedpart rf7 p7_3708r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3709_1, c7_3709_2, c7_3709_3, c7_3709_4, c7_3709_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3710_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3710_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3708l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3710_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3708l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3710_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3708l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3710_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3708l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3710 :
    hubcapFit theRedpart rf7 p7_3708l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3710_1, c7_3710_2, c7_3710_3, c7_3710_4, c7_3710_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3707l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3712_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3707l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3712 :
    hubcapFit theRedpart rf7 p7_3707l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3712_1, c7_3712_2, c7_3712_3, c7_3712_4, c7_3712_5, c7_3712_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3715r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3715r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3715r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3715r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3715r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3716_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3715r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3716 :
    hubcapFit theRedpart rf7 p7_3715r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3716_1, c7_3716_2, c7_3716_3, c7_3716_4, c7_3716_5, c7_3716_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3715l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3715l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3715l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3717_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3715l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3717 :
    hubcapFit theRedpart rf7 p7_3715l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3717_1, c7_3717_2, c7_3717_3, c7_3717_4, c7_3717_5, c7_3717_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3714l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3714l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3714l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3719_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3719 :
    hubcapFit theRedpart rf7 p7_3714l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3719_1, c7_3719_2, c7_3719_3, c7_3719_4, c7_3719_5, c7_3719_6, c7_3719_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3713l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3713l) (hubSubn 7 4 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3713l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3721_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3713l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3721 :
    hubcapFit theRedpart rf7 p7_3713l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 4 1 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3721_1, c7_3721_2, c7_3721_3, c7_3721_4, c7_3721_5, c7_3721_6, c7_3721_7]

end FourColor

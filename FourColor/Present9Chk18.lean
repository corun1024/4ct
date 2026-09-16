import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 18 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_803l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_803l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_817_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_803l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_817 :
    hubcapFit theRedpart rf9 p9_803l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_817_1, c9_817_2, c9_817_3, c9_817_4, c9_817_5, c9_817_6, c9_817_7, c9_817_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_802l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_802l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_802l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_802l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_802l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_802l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_819_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_802l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_819 :
    hubcapFit theRedpart rf9 p9_802l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_819_1, c9_819_2, c9_819_3, c9_819_4, c9_819_5, c9_819_6, c9_819_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_821_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_801l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_821 :
    hubcapFit theRedpart rf9 p9_801l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_821_1, c9_821_2, c9_821_3, c9_821_4, c9_821_5, c9_821_6, c9_821_7, c9_821_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_800l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_800l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_800l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_800l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_800l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_823_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_800l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_823 :
    hubcapFit theRedpart rf9 p9_800l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_823_1, c9_823_2, c9_823_3, c9_823_4, c9_823_5, c9_823_6, c9_823_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_799l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_799l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_825_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_799l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_825 :
    hubcapFit theRedpart rf9 p9_799l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_825_1, c9_825_2, c9_825_3, c9_825_4, c9_825_5, c9_825_6, c9_825_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_857r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_858_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_857r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_858 :
    hubcapFit theRedpart rf9 p9_857r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_858_1, c9_858_2, c9_858_3, c9_858_4, c9_858_5, c9_858_6, c9_858_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_860r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_860r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_860r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_860r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_860r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_860r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_860r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_861_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_860r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_861 :
    hubcapFit theRedpart rf9 p9_860r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_861_1, c9_861_2, c9_861_3, c9_861_4, c9_861_5, c9_861_6, c9_861_7, c9_861_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_860l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_860l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_862_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_860l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_862 :
    hubcapFit theRedpart rf9 p9_860l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_862_1, c9_862_2, c9_862_3, c9_862_4, c9_862_5, c9_862_6, c9_862_7, c9_862_8, c9_862_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_865_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_852l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_865 :
    hubcapFit theRedpart rf9 p9_852l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_865_1, c9_865_2, c9_865_3, c9_865_4, c9_865_5, c9_865_6, c9_865_7, c9_865_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_850l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_850l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_867_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_850l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_867 :
    hubcapFit theRedpart rf9 p9_850l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_867_1, c9_867_2, c9_867_3, c9_867_4, c9_867_5, c9_867_6, c9_867_7, c9_867_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_876r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_876r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_876r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_876r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_876r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_876r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_876r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_877_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_876r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_877 :
    hubcapFit theRedpart rf9 p9_876r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_877_1, c9_877_2, c9_877_3, c9_877_4, c9_877_5, c9_877_6, c9_877_7, c9_877_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_878_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_878 :
    hubcapFit theRedpart rf9 p9_876l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_878_1, c9_878_2, c9_878_3, c9_878_4, c9_878_5, c9_878_6, c9_878_7, c9_878_8, c9_878_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_874l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_874l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_874l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_880_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_874l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_880 :
    hubcapFit theRedpart rf9 p9_874l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_880_1, c9_880_2, c9_880_3, c9_880_4, c9_880_5, c9_880_6, c9_880_7, c9_880_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_882_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_882 :
    hubcapFit theRedpart rf9 p9_871l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_882_1, c9_882_2, c9_882_3, c9_882_4, c9_882_5, c9_882_6, c9_882_7, c9_882_8, c9_882_9]

end FourColor

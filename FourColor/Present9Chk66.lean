import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 66 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3121l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3122_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3121l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3122 :
    hubcapFit theRedpart rf9 p9_3121l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3122_1, c9_3122_2, c9_3122_3, c9_3122_4, c9_3122_5, c9_3122_6, c9_3122_7, c9_3122_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3124l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3125_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3124l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3125 :
    hubcapFit theRedpart rf9 p9_3124l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3125_1, c9_3125_2, c9_3125_3, c9_3125_4, c9_3125_5, c9_3125_6, c9_3125_7, c9_3125_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3124r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3124r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3124r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3124r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3124r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3124r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3124r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3127_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3124r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3127 :
    hubcapFit theRedpart rf9 p9_3124r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3127_1, c9_3127_2, c9_3127_3, c9_3127_4, c9_3127_5, c9_3127_6, c9_3127_7, c9_3127_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3146r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3146r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3146r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3147_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3146r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3147 :
    hubcapFit theRedpart rf9 p9_3146r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3147_1, c9_3147_2, c9_3147_3, c9_3147_4, c9_3147_5, c9_3147_6, c9_3147_7, c9_3147_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3146l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3148_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3146l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3148 :
    hubcapFit theRedpart rf9 p9_3146l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3148_1, c9_3148_2, c9_3148_3, c9_3148_4, c9_3148_5, c9_3148_6, c9_3148_7, c9_3148_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3144l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3144l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3144l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3144l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3144l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3144l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3144l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3144l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3150_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3144l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3150 :
    hubcapFit theRedpart rf9 p9_3144l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3150_1, c9_3150_2, c9_3150_3, c9_3150_4, c9_3150_5, c9_3150_6, c9_3150_7, c9_3150_8, c9_3150_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3143l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3143l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3143l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3152_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3143l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3152 :
    hubcapFit theRedpart rf9 p9_3143l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3152_1, c9_3152_2, c9_3152_3, c9_3152_4, c9_3152_5, c9_3152_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3142l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3142l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3142l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3142l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3153_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3142l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3153 :
    hubcapFit theRedpart rf9 p9_3142l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3153_1, c9_3153_2, c9_3153_3, c9_3153_4, c9_3153_5, c9_3153_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3141l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3141l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3141l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3141l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3141l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3155_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3141l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3155 :
    hubcapFit theRedpart rf9 p9_3141l
    (Hubcap.one 0 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3155_1, c9_3155_2, c9_3155_3, c9_3155_4, c9_3155_5, c9_3155_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3158r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3158r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3158r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3158r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3158r) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3159_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3158r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3159 :
    hubcapFit theRedpart rf9 p9_3158r
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3159_1, c9_3159_2, c9_3159_3, c9_3159_4, c9_3159_5, c9_3159_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3158l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3158l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3160_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3158l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3160 :
    hubcapFit theRedpart rf9 p9_3158l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3160_1, c9_3160_2, c9_3160_3, c9_3160_4, c9_3160_5, c9_3160_6, c9_3160_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3139l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3139l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3139l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3139l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3139l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3163_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3139l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3163 :
    hubcapFit theRedpart rf9 p9_3139l
    (Hubcap.one 3 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3163_1, c9_3163_2, c9_3163_3, c9_3163_4, c9_3163_5, c9_3163_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3138l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3138l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3138l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3138l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3164_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3164 :
    hubcapFit theRedpart rf9 p9_3138l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3164_1, c9_3164_2, c9_3164_3, c9_3164_4, c9_3164_5, c9_3164_6, c9_3164_7, c9_3164_8, c9_3164_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3137l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3137l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3166_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3166 :
    hubcapFit theRedpart rf9 p9_3137l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3166_1, c9_3166_2, c9_3166_3, c9_3166_4, c9_3166_5, c9_3166_6, c9_3166_7, c9_3166_8, c9_3166_9]

end FourColor

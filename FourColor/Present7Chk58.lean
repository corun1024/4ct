import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 58 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3120l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3120l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3120l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3120l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3120l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3135_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3120l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3135 :
    hubcapFit theRedpart rf7 p7_3120l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3135_1, c7_3135_2, c7_3135_3, c7_3135_4, c7_3135_5, c7_3135_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3141_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3140r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3141_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3140r) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3141_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3140r) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3141_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3140r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3141 :
    hubcapFit theRedpart rf7 p7_3140r
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3141_1, c7_3141_2, c7_3141_3, c7_3141_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3142_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3142_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3140l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3142_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3142_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3140l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3142_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3140l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3142 :
    hubcapFit theRedpart rf7 p7_3140l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3142_1, c7_3142_2, c7_3142_3, c7_3142_4, c7_3142_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3144_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3139l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3144_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3139l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3144_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3139l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3144_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3139l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3144_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3139l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3144 :
    hubcapFit theRedpart rf7 p7_3139l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3144_1, c7_3144_2, c7_3144_3, c7_3144_4, c7_3144_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3145_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3138l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3145_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3138l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3145_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3138l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3145_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3138l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3145_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3138l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3145 :
    hubcapFit theRedpart rf7 p7_3138l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3145_1, c7_3145_2, c7_3145_3, c7_3145_4, c7_3145_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3137l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3137l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3137l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3137l) (hubSubn 7 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3137l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3147_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3137l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3147 :
    hubcapFit theRedpart rf7 p7_3137l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3147_1, c7_3147_2, c7_3147_3, c7_3147_4, c7_3147_5, c7_3147_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3152_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3151r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3152_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3151r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3152_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3151r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3152_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3151r) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3152_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3151r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3152 :
    hubcapFit theRedpart rf7 p7_3151r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3152_1, c7_3152_2, c7_3152_3, c7_3152_4, c7_3152_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3151l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3151l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3153_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3151l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3153 :
    hubcapFit theRedpart rf7 p7_3151l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3153_1, c7_3153_2, c7_3153_3, c7_3153_4, c7_3153_5, c7_3153_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3155_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3155_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3150l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3155_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3150l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3155_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3150l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3155_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3150l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3155 :
    hubcapFit theRedpart rf7 p7_3150l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3155_1, c7_3155_2, c7_3155_3, c7_3155_4, c7_3155_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3149l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3156_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3156 :
    hubcapFit theRedpart rf7 p7_3149l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3156_1, c7_3156_2, c7_3156_3, c7_3156_4, c7_3156_5, c7_3156_6, c7_3156_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3161_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3160r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3161_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3160r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3161_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3160r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3161_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3160r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3161_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3160r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3161 :
    hubcapFit theRedpart rf7 p7_3160r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3161_1, c7_3161_2, c7_3161_3, c7_3161_4, c7_3161_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3160l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3160l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3160l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3160l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3160l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3160l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3162_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3162 :
    hubcapFit theRedpart rf7 p7_3160l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3162_1, c7_3162_2, c7_3162_3, c7_3162_4, c7_3162_5, c7_3162_6, c7_3162_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3164_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3159l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3164_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3159l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3164_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3159l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3164_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3159l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3164_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3159l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3164 :
    hubcapFit theRedpart rf7 p7_3159l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3164_1, c7_3164_2, c7_3164_3, c7_3164_4, c7_3164_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3158l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3158l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3158l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3158l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3158l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3165_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3158l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3165 :
    hubcapFit theRedpart rf7 p7_3158l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3165_1, c7_3165_2, c7_3165_3, c7_3165_4, c7_3165_5, c7_3165_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3167_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3167_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2998l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3167_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2998l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3167_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2998l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3167_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2998l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3167 :
    hubcapFit theRedpart rf7 p7_2998l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3167_1, c7_3167_2, c7_3167_3, c7_3167_4, c7_3167_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2997l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2997l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2997l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2997l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2997l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3169_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2997l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3169 :
    hubcapFit theRedpart rf7 p7_2997l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3169_1, c7_3169_2, c7_3169_3, c7_3169_4, c7_3169_5, c7_3169_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3184r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3184r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3184r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3184r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3184r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3184r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3185_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3184r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3185 :
    hubcapFit theRedpart rf7 p7_3184r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3185_1, c7_3185_2, c7_3185_3, c7_3185_4, c7_3185_5, c7_3185_6, c7_3185_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3184l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3184l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3184l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3184l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3184l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3184l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3186_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3184l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3186 :
    hubcapFit theRedpart rf7 p7_3184l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3186_1, c7_3186_2, c7_3186_3, c7_3186_4, c7_3186_5, c7_3186_6, c7_3186_7]

end FourColor

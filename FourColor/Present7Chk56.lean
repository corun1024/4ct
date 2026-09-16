import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 56 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3041_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3041_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3007l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3041_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3041_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3007l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3041_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3007l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3041 :
    hubcapFit theRedpart rf7 p7_3007l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3041_1, c7_3041_2, c7_3041_3, c7_3041_4, c7_3041_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3042_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3042 :
    hubcapFit theRedpart rf7 p7_3006l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3042_1, c7_3042_2, c7_3042_3, c7_3042_4, c7_3042_5, c7_3042_6, c7_3042_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3044_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3005l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3044_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3005l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3044_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3005l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3044_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3005l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3044_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3005l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3044 :
    hubcapFit theRedpart rf7 p7_3005l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3044_1, c7_3044_2, c7_3044_3, c7_3044_4, c7_3044_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3047_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3046r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3047_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3046r) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3047_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3046r) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3047_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3046r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3047 :
    hubcapFit theRedpart rf7 p7_3046r
    (Hubcap.one 1 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3047_1, c7_3047_2, c7_3047_3, c7_3047_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3048_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3046l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3048_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3046l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3048_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3046l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3048_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3046l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3048_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3046l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3048 :
    hubcapFit theRedpart rf7 p7_3046l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3048_1, c7_3048_2, c7_3048_3, c7_3048_4, c7_3048_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3050_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3045l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3050_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3045l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3050_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3045l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3050_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3045l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3050_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3045l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3050 :
    hubcapFit theRedpart rf7 p7_3045l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3050_1, c7_3050_2, c7_3050_3, c7_3050_4, c7_3050_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3052_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3052_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3003l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3052_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3003l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3052_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3003l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3052_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3003l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3052 :
    hubcapFit theRedpart rf7 p7_3003l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3052_1, c7_3052_2, c7_3052_3, c7_3052_4, c7_3052_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3002l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3002l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3002l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3002l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3002l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3053_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3002l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3053 :
    hubcapFit theRedpart rf7 p7_3002l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3053_1, c7_3053_2, c7_3053_3, c7_3053_4, c7_3053_5, c7_3053_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3061r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3061r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3061r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3061r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3061r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3062_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3061r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3062 :
    hubcapFit theRedpart rf7 p7_3061r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3062_1, c7_3062_2, c7_3062_3, c7_3062_4, c7_3062_5, c7_3062_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3063_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3063_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3061l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3063_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3063_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3061l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3063_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3061l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3063 :
    hubcapFit theRedpart rf7 p7_3061l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3063_1, c7_3063_2, c7_3063_3, c7_3063_4, c7_3063_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3065_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3065_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3060l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3065_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3065_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3060l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3065_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3060l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3065 :
    hubcapFit theRedpart rf7 p7_3060l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3065_1, c7_3065_2, c7_3065_3, c7_3065_4, c7_3065_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3059l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3059l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3059l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3066_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3059l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3066 :
    hubcapFit theRedpart rf7 p7_3059l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3066_1, c7_3066_2, c7_3066_3, c7_3066_4, c7_3066_5, c7_3066_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3068_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3058l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3068_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3058l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3068_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3058l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3068_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3058l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3068_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3058l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3068 :
    hubcapFit theRedpart rf7 p7_3058l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3068_1, c7_3068_2, c7_3068_3, c7_3068_4, c7_3068_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3057l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3057l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3057l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3069_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3057l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3069 :
    hubcapFit theRedpart rf7 p7_3057l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3069_1, c7_3069_2, c7_3069_3, c7_3069_4, c7_3069_5, c7_3069_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3056l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3056l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3056l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3056l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3056l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3071_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3056l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3071 :
    hubcapFit theRedpart rf7 p7_3056l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3071_1, c7_3071_2, c7_3071_3, c7_3071_4, c7_3071_5, c7_3071_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3072_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3055l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3072_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3055l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3072_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3055l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3072_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3055l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3072_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3055l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3072 :
    hubcapFit theRedpart rf7 p7_3055l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3072_1, c7_3072_2, c7_3072_3, c7_3072_4, c7_3072_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3074_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3000l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3074 :
    hubcapFit theRedpart rf7 p7_3000l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3074_1, c7_3074_2, c7_3074_3, c7_3074_4, c7_3074_5, c7_3074_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3089r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3089r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3089r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3089r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3089r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3089r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3090_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3089r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3090 :
    hubcapFit theRedpart rf7 p7_3089r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3090_1, c7_3090_2, c7_3090_3, c7_3090_4, c7_3090_5, c7_3090_6, c7_3090_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3089l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3089l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3089l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3091_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3089l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3091 :
    hubcapFit theRedpart rf7 p7_3089l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3091_1, c7_3091_2, c7_3091_3, c7_3091_4, c7_3091_5, c7_3091_6]

end FourColor

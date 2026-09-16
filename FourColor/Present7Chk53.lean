import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 53 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2886l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2886l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2886l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2886l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2886l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2888_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2886l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2888 :
    hubcapFit theRedpart rf7 p7_2886l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2888_1, c7_2888_2, c7_2888_3, c7_2888_4, c7_2888_5, c7_2888_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2885l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2885l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2885l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2885l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2885l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2890_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2885l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2890 :
    hubcapFit theRedpart rf7 p7_2885l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2890_1, c7_2890_2, c7_2890_3, c7_2890_4, c7_2890_5, c7_2890_6, c7_2890_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2895r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2895r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2895r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2895r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2896_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2895r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2896 :
    hubcapFit theRedpart rf7 p7_2895r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2896_1, c7_2896_2, c7_2896_3, c7_2896_4, c7_2896_5, c7_2896_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2895l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2895l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2895l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2897_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2895l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2897 :
    hubcapFit theRedpart rf7 p7_2895l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2897_1, c7_2897_2, c7_2897_3, c7_2897_4, c7_2897_5, c7_2897_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2899r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2899r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2899r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2900_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2899r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2900 :
    hubcapFit theRedpart rf7 p7_2899r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2900_1, c7_2900_2, c7_2900_3, c7_2900_4, c7_2900_5, c7_2900_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2899l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2899l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2901_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2901 :
    hubcapFit theRedpart rf7 p7_2899l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2901_1, c7_2901_2, c7_2901_3, c7_2901_4, c7_2901_5, c7_2901_6, c7_2901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2893l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2893l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2893l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2903_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2893l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2903 :
    hubcapFit theRedpart rf7 p7_2893l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2903_1, c7_2903_2, c7_2903_3, c7_2903_4, c7_2903_5, c7_2903_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2905_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2892l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2905 :
    hubcapFit theRedpart rf7 p7_2892l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2905_1, c7_2905_2, c7_2905_3, c7_2905_4, c7_2905_5, c7_2905_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2907_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2837l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2907_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2837l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2907_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2907_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2837l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2907_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2837l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2907 :
    hubcapFit theRedpart rf7 p7_2837l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2907_1, c7_2907_2, c7_2907_3, c7_2907_4, c7_2907_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2920r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2920r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2920r) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2920r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2920r) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2921_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2920r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2921 :
    hubcapFit theRedpart rf7 p7_2920r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2921_1, c7_2921_2, c7_2921_3, c7_2921_4, c7_2921_5, c7_2921_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2920l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2920l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2920l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2920l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2922_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2920l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2922 :
    hubcapFit theRedpart rf7 p7_2920l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2922_1, c7_2922_2, c7_2922_3, c7_2922_4, c7_2922_5, c7_2922_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2924_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2924_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2924_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2919l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2924_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2919l) (hubSubn 7 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2924_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2919l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2924 :
    hubcapFit theRedpart rf7 p7_2919l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2924_1, c7_2924_2, c7_2924_3, c7_2924_4, c7_2924_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2918l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2918l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2925_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2918l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2925 :
    hubcapFit theRedpart rf7 p7_2918l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2925_1, c7_2925_2, c7_2925_3, c7_2925_4, c7_2925_5, c7_2925_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2927_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2917l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2927_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2917l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2927_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2917l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2927_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2917l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2927_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2917l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2927 :
    hubcapFit theRedpart rf7 p7_2917l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2927_1, c7_2927_2, c7_2927_3, c7_2927_4, c7_2927_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2914l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2914l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2914l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2914l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2929_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2914l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2929 :
    hubcapFit theRedpart rf7 p7_2914l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2929_1, c7_2929_2, c7_2929_3, c7_2929_4, c7_2929_5, c7_2929_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2931_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2931_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2913l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2931_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2913l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2931_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2913l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2931_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2913l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2931 :
    hubcapFit theRedpart rf7 p7_2913l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2931_1, c7_2931_2, c7_2931_3, c7_2931_4, c7_2931_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2932_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2912l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2932_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2932_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2932_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2912l) (hubSubn 7 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2932_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2912l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2932 :
    hubcapFit theRedpart rf7 p7_2912l
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2932_1, c7_2932_2, c7_2932_3, c7_2932_4, c7_2932_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2936r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2936r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2936r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2936r) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2936r) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2937_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2936r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2937 :
    hubcapFit theRedpart rf7 p7_2936r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2937_1, c7_2937_2, c7_2937_3, c7_2937_4, c7_2937_5, c7_2937_6]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 57 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2905l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2905l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2905l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2905l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2905l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2907_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2905l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2907 :
    hubcapFit theRedpart rf8 p8_2905l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2907_1, c8_2907_2, c8_2907_3, c8_2907_4, c8_2907_5, c8_2907_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2903l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2903l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2903l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2903l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2903l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2909_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2903l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2909 :
    hubcapFit theRedpart rf8 p8_2903l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2909_1, c8_2909_2, c8_2909_3, c8_2909_4, c8_2909_5, c8_2909_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2902l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2902l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2902l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2902l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2902l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2911_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2902l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2911 :
    hubcapFit theRedpart rf8 p8_2902l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2911_1, c8_2911_2, c8_2911_3, c8_2911_4, c8_2911_5, c8_2911_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2914_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2880l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2914_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2880l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2914_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2880l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2914_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2880l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2914_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2880l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2914 :
    hubcapFit theRedpart rf8 p8_2880l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2914_1, c8_2914_2, c8_2914_3, c8_2914_4, c8_2914_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2915_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2879l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2915_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2879l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2915_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2879l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2915_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2879l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2915_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2879l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2915 :
    hubcapFit theRedpart rf8 p8_2879l
    (Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2915_1, c8_2915_2, c8_2915_3, c8_2915_4, c8_2915_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2930r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2930r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2930r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2930r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2930r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2930r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2930r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2931_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2930r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2931 :
    hubcapFit theRedpart rf8 p8_2930r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2931_1, c8_2931_2, c8_2931_3, c8_2931_4, c8_2931_5, c8_2931_6, c8_2931_7, c8_2931_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2930l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2930l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2930l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2930l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2932_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2930l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2932 :
    hubcapFit theRedpart rf8 p8_2930l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2932_1, c8_2932_2, c8_2932_3, c8_2932_4, c8_2932_5, c8_2932_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2929l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2929l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2929l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2929l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2929l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2929l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2934_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2929l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2934 :
    hubcapFit theRedpart rf8 p8_2929l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2934_1, c8_2934_2, c8_2934_3, c8_2934_4, c8_2934_5, c8_2934_6, c8_2934_7, c8_2934_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2928l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2928l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2928l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2928l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2928l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2936_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2928l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2936 :
    hubcapFit theRedpart rf8 p8_2928l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2936_1, c8_2936_2, c8_2936_3, c8_2936_4, c8_2936_5, c8_2936_6, c8_2936_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2927l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2927l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2927l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2927l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2927l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2938_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2938 :
    hubcapFit theRedpart rf8 p8_2927l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2938_1, c8_2938_2, c8_2938_3, c8_2938_4, c8_2938_5, c8_2938_6, c8_2938_7, c8_2938_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2940_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2926l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2940 :
    hubcapFit theRedpart rf8 p8_2926l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2940_1, c8_2940_2, c8_2940_3, c8_2940_4, c8_2940_5, c8_2940_6, c8_2940_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2924l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2924l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2942_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2924l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2942 :
    hubcapFit theRedpart rf8 p8_2924l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2942_1, c8_2942_2, c8_2942_3, c8_2942_4, c8_2942_5, c8_2942_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2922l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2922l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2922l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2922l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2922l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2922l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2944_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2922l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2944 :
    hubcapFit theRedpart rf8 p8_2922l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2944_1, c8_2944_2, c8_2944_3, c8_2944_4, c8_2944_5, c8_2944_6, c8_2944_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2946_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2946_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2920l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2946_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2920l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2946_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2920l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2946_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2920l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2946 :
    hubcapFit theRedpart rf8 p8_2920l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2946_1, c8_2946_2, c8_2946_3, c8_2946_4, c8_2946_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2948_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2948_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2948_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2919l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2948_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2919l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2948_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2919l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2948 :
    hubcapFit theRedpart rf8 p8_2919l
    (Hubcap.one 1 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2948_1, c8_2948_2, c8_2948_3, c8_2948_4, c8_2948_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2918l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2918l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2918l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2918l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2949_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2918l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2949 :
    hubcapFit theRedpart rf8 p8_2918l
    (Hubcap.one 7 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2949_1, c8_2949_2, c8_2949_3, c8_2949_4, c8_2949_5, c8_2949_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2956_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2955r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2956_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2955r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2956_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2955r) (hubSubn 8 7 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2956_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2955r) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2956_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2955r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2956 :
    hubcapFit theRedpart rf8 p8_2955r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2956_1, c8_2956_2, c8_2956_3, c8_2956_4, c8_2956_5]

end FourColor

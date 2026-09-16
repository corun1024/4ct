import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 111 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5905r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5905r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5905r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5905r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5905r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5905r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5906_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5905r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5906 :
    hubcapFit theRedpart rf7 p7_5905r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5906_1, c7_5906_2, c7_5906_3, c7_5906_4, c7_5906_5, c7_5906_6, c7_5906_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5905l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5905l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5905l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5905l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5905l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5905l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5907_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5905l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5907 :
    hubcapFit theRedpart rf7 p7_5905l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5907_1, c7_5907_2, c7_5907_3, c7_5907_4, c7_5907_5, c7_5907_6, c7_5907_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5904l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5904l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5904l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5904l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5904l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5909_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5904l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5909 :
    hubcapFit theRedpart rf7 p7_5904l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5909_1, c7_5909_2, c7_5909_3, c7_5909_4, c7_5909_5, c7_5909_6, c7_5909_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5903l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5903l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5903l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5903l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5903l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5903l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5911_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5903l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5911 :
    hubcapFit theRedpart rf7 p7_5903l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5911_1, c7_5911_2, c7_5911_3, c7_5911_4, c7_5911_5, c7_5911_6, c7_5911_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5902l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5902l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5902l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5902l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5902l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5902l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5913_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5902l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5913 :
    hubcapFit theRedpart rf7 p7_5902l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5913_1, c7_5913_2, c7_5913_3, c7_5913_4, c7_5913_5, c7_5913_6, c7_5913_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5901l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5901l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5901l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5901l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5901l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5901l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5915_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5901l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5915 :
    hubcapFit theRedpart rf7 p7_5901l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5915_1, c7_5915_2, c7_5915_3, c7_5915_4, c7_5915_5, c7_5915_6, c7_5915_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5899l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5899l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5899l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5899l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5899l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5917_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5917 :
    hubcapFit theRedpart rf7 p7_5899l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5917_1, c7_5917_2, c7_5917_3, c7_5917_4, c7_5917_5, c7_5917_6, c7_5917_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5832l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5832l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5832l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5832l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5832l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5920_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5832l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5920 :
    hubcapFit theRedpart rf7 p7_5832l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5920_1, c7_5920_2, c7_5920_3, c7_5920_4, c7_5920_5, c7_5920_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5927r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5927r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5927r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5927r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5927r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5927r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5928_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5927r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5928 :
    hubcapFit theRedpart rf7 p7_5927r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5928_1, c7_5928_2, c7_5928_3, c7_5928_4, c7_5928_5, c7_5928_6, c7_5928_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5927l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5927l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5927l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5927l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5927l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5929_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5927l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5929 :
    hubcapFit theRedpart rf7 p7_5927l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5929_1, c7_5929_2, c7_5929_3, c7_5929_4, c7_5929_5, c7_5929_6, c7_5929_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5926l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5926l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5926l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5926l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5926l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5931_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5931 :
    hubcapFit theRedpart rf7 p7_5926l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5931_1, c7_5931_2, c7_5931_3, c7_5931_4, c7_5931_5, c7_5931_6, c7_5931_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5925l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5925l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5925l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5925l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5925l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5933_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5925l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5933 :
    hubcapFit theRedpart rf7 p7_5925l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5933_1, c7_5933_2, c7_5933_3, c7_5933_4, c7_5933_5, c7_5933_6, c7_5933_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5923l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5923l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5923l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5923l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5923l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5923l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5935_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5923l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5935 :
    hubcapFit theRedpart rf7 p7_5923l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5935_1, c7_5935_2, c7_5935_3, c7_5935_4, c7_5935_5, c7_5935_6, c7_5935_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5938_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5830l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5938_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5830l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5938_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5830l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5938_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5830l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5938_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5830l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5938 :
    hubcapFit theRedpart rf7 p7_5830l
    (Hubcap.one 0 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5938_1, c7_5938_2, c7_5938_3, c7_5938_4, c7_5938_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5940_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5939r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5940_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5939r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5940_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5939r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5940_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5939r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5940_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5939r) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5940 :
    hubcapFit theRedpart rf7 p7_5939r
    (Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5940_1, c7_5940_2, c7_5940_3, c7_5940_4, c7_5940_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5946r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5946r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5946r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5946r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5946r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5947_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5946r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5947 :
    hubcapFit theRedpart rf7 p7_5946r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-4) <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-4) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5947_1, c7_5947_2, c7_5947_3, c7_5947_4, c7_5947_5, c7_5947_6]

end FourColor

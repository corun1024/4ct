import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 57 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3088l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3088l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3088l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3093_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3088l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3093 :
    hubcapFit theRedpart rf7 p7_3088l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3093_1, c7_3093_2, c7_3093_3, c7_3093_4, c7_3093_5, c7_3093_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3087l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3087l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3087l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3094_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3087l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3094 :
    hubcapFit theRedpart rf7 p7_3087l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3094_1, c7_3094_2, c7_3094_3, c7_3094_4, c7_3094_5, c7_3094_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3096_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3085l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3096_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3085l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3096_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3085l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3096_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3085l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3096 :
    hubcapFit theRedpart rf7 p7_3085l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3096_1, c7_3096_2, c7_3096_3, c7_3096_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3098_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3084l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3098_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3084l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3098_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3084l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3098_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3084l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3098_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3084l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3098 :
    hubcapFit theRedpart rf7 p7_3084l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3098_1, c7_3098_2, c7_3098_3, c7_3098_4, c7_3098_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3100r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3100r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3100r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3100r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3100r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3101_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3100r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3101 :
    hubcapFit theRedpart rf7 p7_3100r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3101_1, c7_3101_2, c7_3101_3, c7_3101_4, c7_3101_5, c7_3101_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3102_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3100l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3102_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3100l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3102_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3100l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3102_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3100l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3102_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3100l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3102 :
    hubcapFit theRedpart rf7 p7_3100l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3102_1, c7_3102_2, c7_3102_3, c7_3102_4, c7_3102_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3099l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3099l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3099l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3099l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3099l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3104_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3099l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3104 :
    hubcapFit theRedpart rf7 p7_3099l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3104_1, c7_3104_2, c7_3104_3, c7_3104_4, c7_3104_5, c7_3104_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3107r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3107r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3107r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3107r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3107r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3108_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3107r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3108 :
    hubcapFit theRedpart rf7 p7_3107r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3108_1, c7_3108_2, c7_3108_3, c7_3108_4, c7_3108_5, c7_3108_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3109_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3107l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3109_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3107l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3109_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3107l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3109_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3107l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3109_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3107l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3109 :
    hubcapFit theRedpart rf7 p7_3107l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3109_1, c7_3109_2, c7_3109_3, c7_3109_4, c7_3109_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3111_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3081l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3111_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3081l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3111_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3081l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3111_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3081l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3111 :
    hubcapFit theRedpart rf7 p7_3081l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3111_1, c7_3111_2, c7_3111_3, c7_3111_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3115_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3114r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3115_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3114r) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3115_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3114r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3115_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3114r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3115 :
    hubcapFit theRedpart rf7 p7_3114r
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3115_1, c7_3115_2, c7_3115_3, c7_3115_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3116_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3114l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3116_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3114l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3116_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3114l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3116_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3114l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3116 :
    hubcapFit theRedpart rf7 p7_3114l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3116_1, c7_3116_2, c7_3116_3, c7_3116_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3113l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3113l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3113l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3118_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3113l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3118 :
    hubcapFit theRedpart rf7 p7_3113l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3118_1, c7_3118_2, c7_3118_3, c7_3118_4, c7_3118_5, c7_3118_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3124_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3123r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3124_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3123r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3124_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3123r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3124_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3123r) (hubSubn 7 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3124_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3123r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3124 :
    hubcapFit theRedpart rf7 p7_3123r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3124_1, c7_3124_2, c7_3124_3, c7_3124_4, c7_3124_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3123l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3123l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3125_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3123l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3125 :
    hubcapFit theRedpart rf7 p7_3123l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3125_1, c7_3125_2, c7_3125_3, c7_3125_4, c7_3125_5, c7_3125_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3127_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3122l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3127_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3122l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3127_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3122l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3127_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3122l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3127_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3122l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3127 :
    hubcapFit theRedpart rf7 p7_3122l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3127_1, c7_3127_2, c7_3127_3, c7_3127_4, c7_3127_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3129r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3129r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3129r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3129r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3129r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3130_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3129r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3130 :
    hubcapFit theRedpart rf7 p7_3129r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3130_1, c7_3130_2, c7_3130_3, c7_3130_4, c7_3130_5, c7_3130_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3131_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3129l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3131 :
    hubcapFit theRedpart rf7 p7_3129l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3131_1, c7_3131_2, c7_3131_3, c7_3131_4, c7_3131_5, c7_3131_6, c7_3131_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3128l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3128l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3128l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3128l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3128l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3133_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3128l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3133 :
    hubcapFit theRedpart rf7 p7_3128l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3133_1, c7_3133_2, c7_3133_3, c7_3133_4, c7_3133_5, c7_3133_6]

end FourColor

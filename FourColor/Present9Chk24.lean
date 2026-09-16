import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 24 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1112l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1112l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1112l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1114_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1112l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1114 :
    hubcapFit theRedpart rf9 p9_1112l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1114_1, c9_1114_2, c9_1114_3, c9_1114_4, c9_1114_5, c9_1114_6, c9_1114_7, c9_1114_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1111l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1111l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1111l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1111l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1111l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1111l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1111l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1116_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1111l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1116 :
    hubcapFit theRedpart rf9 p9_1111l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1116_1, c9_1116_2, c9_1116_3, c9_1116_4, c9_1116_5, c9_1116_6, c9_1116_7, c9_1116_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1110l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1110l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1110l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1110l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1110l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1110l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1110l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1118_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1110l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1118 :
    hubcapFit theRedpart rf9 p9_1110l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1118_1, c9_1118_2, c9_1118_3, c9_1118_4, c9_1118_5, c9_1118_6, c9_1118_7, c9_1118_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1017l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1017l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1120_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1017l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1120 :
    hubcapFit theRedpart rf9 p9_1017l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1120_1, c9_1120_2, c9_1120_3, c9_1120_4, c9_1120_5, c9_1120_6, c9_1120_7, c9_1120_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1016l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1016l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1122_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1016l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1122 :
    hubcapFit theRedpart rf9 p9_1016l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1122_1, c9_1122_2, c9_1122_3, c9_1122_4, c9_1122_5, c9_1122_6, c9_1122_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1124l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1124l) (hubSubn 9 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1125_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1124l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1125 :
    hubcapFit theRedpart rf9 p9_1124l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1125_1, c9_1125_2, c9_1125_3, c9_1125_4, c9_1125_5, c9_1125_6, c9_1125_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1124r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1124r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1124r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1124r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1124r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1124r) (hubSubn 9 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1127_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1124r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1127 :
    hubcapFit theRedpart rf9 p9_1124r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1127_1, c9_1127_2, c9_1127_3, c9_1127_4, c9_1127_5, c9_1127_6, c9_1127_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1153r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1153r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1153r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1153r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1153r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1154_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1153r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1154 :
    hubcapFit theRedpart rf9 p9_1153r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1154_1, c9_1154_2, c9_1154_3, c9_1154_4, c9_1154_5, c9_1154_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1153l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1153l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1155_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1153l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1155 :
    hubcapFit theRedpart rf9 p9_1153l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1155_1, c9_1155_2, c9_1155_3, c9_1155_4, c9_1155_5, c9_1155_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1151l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1157_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1151l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1157 :
    hubcapFit theRedpart rf9 p9_1151l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1157_1, c9_1157_2, c9_1157_3, c9_1157_4, c9_1157_5, c9_1157_6, c9_1157_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1148l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1159_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1148l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1159 :
    hubcapFit theRedpart rf9 p9_1148l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1159_1, c9_1159_2, c9_1159_3, c9_1159_4, c9_1159_5, c9_1159_6, c9_1159_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1147l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1147l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1147l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1147l) (hubSubn 9 7 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1161_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1147l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1161 :
    hubcapFit theRedpart rf9 p9_1147l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1161_1, c9_1161_2, c9_1161_3, c9_1161_4, c9_1161_5, c9_1161_6, c9_1161_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1163_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1146l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1163 :
    hubcapFit theRedpart rf9 p9_1146l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1163_1, c9_1163_2, c9_1163_3, c9_1163_4, c9_1163_5, c9_1163_6, c9_1163_7, c9_1163_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1165l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1165l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1165l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1166_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1165l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1166 :
    hubcapFit theRedpart rf9 p9_1165l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1166_1, c9_1166_2, c9_1166_3, c9_1166_4, c9_1166_5, c9_1166_6, c9_1166_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1165r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1165r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1165r) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1168_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1165r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1168 :
    hubcapFit theRedpart rf9 p9_1165r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1168_1, c9_1168_2, c9_1168_3, c9_1168_4, c9_1168_5, c9_1168_6, c9_1168_7]

end FourColor

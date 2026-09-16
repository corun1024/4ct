import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_133l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_135_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_135 :
    hubcapFit theRedpart rf11 p11_133l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_135_1, c11_135_2, c11_135_3, c11_135_4, c11_135_5, c11_135_6, c11_135_7, c11_135_8, c11_135_9, c11_135_10, c11_135_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_130l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_130l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_130l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_130l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_138_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_130l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_138 :
    hubcapFit theRedpart rf11 p11_130l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_138_1, c11_138_2, c11_138_3, c11_138_4, c11_138_5, c11_138_6, c11_138_7, c11_138_8, c11_138_9, c11_138_10, c11_138_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_122l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_141_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_141 :
    hubcapFit theRedpart rf11 p11_122l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_141_1, c11_141_2, c11_141_3, c11_141_4, c11_141_5, c11_141_6, c11_141_7, c11_141_8, c11_141_9, c11_141_10, c11_141_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_120l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_120l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_120l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_120l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_120l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_143_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_120l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_143 :
    hubcapFit theRedpart rf11 p11_120l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_143_1, c11_143_2, c11_143_3, c11_143_4, c11_143_5, c11_143_6, c11_143_7, c11_143_8, c11_143_9, c11_143_10, c11_143_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_146_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_146 :
    hubcapFit theRedpart rf11 p11_118l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_146_1, c11_146_2, c11_146_3, c11_146_4, c11_146_5, c11_146_6, c11_146_7, c11_146_8, c11_146_9, c11_146_10, c11_146_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_148_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_148 :
    hubcapFit theRedpart rf11 p11_116l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_148_1, c11_148_2, c11_148_3, c11_148_4, c11_148_5, c11_148_6, c11_148_7, c11_148_8, c11_148_9, c11_148_10, c11_148_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_115l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_151_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_151 :
    hubcapFit theRedpart rf11 p11_115l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_151_1, c11_151_2, c11_151_3, c11_151_4, c11_151_5, c11_151_6, c11_151_7, c11_151_8, c11_151_9, c11_151_10, c11_151_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_153_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_153 :
    hubcapFit theRedpart rf11 p11_114l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_153_1, c11_153_2, c11_153_3, c11_153_4, c11_153_5, c11_153_6, c11_153_7, c11_153_8, c11_153_9, c11_153_10, c11_153_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_169r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_169r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_169r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_169r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_169r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_169r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_169r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_169r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_169r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_170_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_169r) (hubSubn 11 7 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_170 :
    hubcapFit theRedpart rf11 p11_169r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 7 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_170_1, c11_170_2, c11_170_3, c11_170_4, c11_170_5, c11_170_6, c11_170_7, c11_170_8, c11_170_9, c11_170_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_175r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_175r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_175r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_175r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_175r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_176_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 5 p11_175r) (hubSubn 11 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_176 :
    hubcapFit theRedpart rf11 p11_175r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_176_1, c11_176_2, c11_176_3, c11_176_4, c11_176_5, c11_176_6, c11_176_7, c11_176_8, c11_176_9, c11_176_10]

end FourColor

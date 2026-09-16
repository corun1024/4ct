import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_177_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_177 :
    hubcapFit theRedpart rf11 p11_175l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_177_1, c11_177_2, c11_177_3, c11_177_4, c11_177_5, c11_177_6, c11_177_7, c11_177_8, c11_177_9, c11_177_10, c11_177_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_180_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_180 :
    hubcapFit theRedpart rf11 p11_172l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_180_1, c11_180_2, c11_180_3, c11_180_4, c11_180_5, c11_180_6, c11_180_7, c11_180_8, c11_180_9, c11_180_10, c11_180_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_183_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_183 :
    hubcapFit theRedpart rf11 p11_164l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_183_1, c11_183_2, c11_183_3, c11_183_4, c11_183_5, c11_183_6, c11_183_7, c11_183_8, c11_183_9, c11_183_10, c11_183_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_162l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_185_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_185 :
    hubcapFit theRedpart rf11 p11_162l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_185_1, c11_185_2, c11_185_3, c11_185_4, c11_185_5, c11_185_6, c11_185_7, c11_185_8, c11_185_9, c11_185_10, c11_185_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_188_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_188 :
    hubcapFit theRedpart rf11 p11_160l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_188_1, c11_188_2, c11_188_3, c11_188_4, c11_188_5, c11_188_6, c11_188_7, c11_188_8, c11_188_9, c11_188_10, c11_188_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_158l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_190_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_158l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_190 :
    hubcapFit theRedpart rf11 p11_158l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_190_1, c11_190_2, c11_190_3, c11_190_4, c11_190_5, c11_190_6, c11_190_7, c11_190_8, c11_190_9, c11_190_10, c11_190_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_157l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_157l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_157l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_193_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 8 p11_157l) (hubSubn 11 10 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_193 :
    hubcapFit theRedpart rf11 p11_157l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 9 5 <|
     Hubcap.two 8 10 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_193_1, c11_193_2, c11_193_3, c11_193_4, c11_193_5, c11_193_6, c11_193_7, c11_193_8, c11_193_9, c11_193_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_209r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_209r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_209r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_209r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_209r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_209r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_209r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_209r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_209r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_210_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 4 p11_209r) (hubSubn 11 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_210 :
    hubcapFit theRedpart rf11 p11_209r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_210_1, c11_210_2, c11_210_3, c11_210_4, c11_210_5, c11_210_6, c11_210_7, c11_210_8, c11_210_9, c11_210_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_211_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_211 :
    hubcapFit theRedpart rf11 p11_209l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_211_1, c11_211_2, c11_211_3, c11_211_4, c11_211_5, c11_211_6, c11_211_7, c11_211_8, c11_211_9, c11_211_10, c11_211_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_217r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_217r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_217r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_217r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_217r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_218_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 5 p11_217r) (hubSubn 11 8 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_218 :
    hubcapFit theRedpart rf11 p11_217r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 8 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_218_1, c11_218_2, c11_218_3, c11_218_4, c11_218_5, c11_218_6, c11_218_7, c11_218_8, c11_218_9, c11_218_10]

end FourColor

import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_176r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_176r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_176r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_176r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_177_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_176r) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_177 :
    hubcapFit theRedpart rf10 p10_176r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_177_1, c10_177_2, c10_177_3, c10_177_4, c10_177_5, c10_177_6, c10_177_7, c10_177_8, c10_177_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_176l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_178_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_176l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_178 :
    hubcapFit theRedpart rf10 p10_176l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_178_1, c10_178_2, c10_178_3, c10_178_4, c10_178_5, c10_178_6, c10_178_7, c10_178_8, c10_178_9, c10_178_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_174l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_174l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_174l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_181_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_181 :
    hubcapFit theRedpart rf10 p10_174l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_181_1, c10_181_2, c10_181_3, c10_181_4, c10_181_5, c10_181_6, c10_181_7, c10_181_8, c10_181_9, c10_181_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_170l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_170l) (hubSubn 10 8 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_170l) (hubSubn 10 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_184_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_170l) (hubSubn 10 7 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_184 :
    hubcapFit theRedpart rf10 p10_170l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 1 8 8 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 7 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_184_1, c10_184_2, c10_184_3, c10_184_4, c10_184_5, c10_184_6, c10_184_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_155l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_155l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_155l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_155l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_155l) (hubSubn 10 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_155l) (hubSubn 10 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_187_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_155l) (hubSubn 10 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_187 :
    hubcapFit theRedpart rf10 p10_155l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 9 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_187_1, c10_187_2, c10_187_3, c10_187_4, c10_187_5, c10_187_6, c10_187_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_153l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_153l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_153l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_153l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_189_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_153l) (hubSubn 10 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_189 :
    hubcapFit theRedpart rf10 p10_153l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 9 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_189_1, c10_189_2, c10_189_3, c10_189_4, c10_189_5, c10_189_6, c10_189_7, c10_189_8, c10_189_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_151l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_151l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_191_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_151l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_191 :
    hubcapFit theRedpart rf10 p10_151l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_191_1, c10_191_2, c10_191_3, c10_191_4, c10_191_5, c10_191_6, c10_191_7, c10_191_8, c10_191_9, c10_191_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_150l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_150l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_150l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_150l) (hubSubn 10 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_150l) (hubSubn 10 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_193_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_150l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_193 :
    hubcapFit theRedpart rf10 p10_150l
    (Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_193_1, c10_193_2, c10_193_3, c10_193_4, c10_193_5, c10_193_6, c10_193_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_203r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_203r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_203r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_203r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_203r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_203r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_203r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_203r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_204_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_203r) (hubSubn 10 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_204 :
    hubcapFit theRedpart rf10 p10_203r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_204_1, c10_204_2, c10_204_3, c10_204_4, c10_204_5, c10_204_6, c10_204_7, c10_204_8, c10_204_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_205_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_205 :
    hubcapFit theRedpart rf10 p10_203l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_205_1, c10_205_2, c10_205_3, c10_205_4, c10_205_5, c10_205_6, c10_205_7, c10_205_8, c10_205_9, c10_205_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_202l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_202l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_202l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_202l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_202l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_208_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_202l) (hubSubn 10 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_208 :
    hubcapFit theRedpart rf10 p10_202l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_208_1, c10_208_2, c10_208_3, c10_208_4, c10_208_5, c10_208_6, c10_208_7, c10_208_8, c10_208_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_200l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_200l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_210_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_200l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_210 :
    hubcapFit theRedpart rf10 p10_200l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_210_1, c10_210_2, c10_210_3, c10_210_4, c10_210_5, c10_210_6, c10_210_7, c10_210_8, c10_210_9, c10_210_10]

end FourColor

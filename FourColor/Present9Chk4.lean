import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_156l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_156l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_156l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_156l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_156l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_185_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_156l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_185 :
    hubcapFit theRedpart rf9 p9_156l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_185_1, c9_185_2, c9_185_3, c9_185_4, c9_185_5, c9_185_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_155l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_155l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_155l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_155l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_155l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_187_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_155l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_187 :
    hubcapFit theRedpart rf9 p9_155l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_187_1, c9_187_2, c9_187_3, c9_187_4, c9_187_5, c9_187_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_188_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_154l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_188_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_154l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_188_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_154l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_188_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_154l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_188_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_154l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_188 :
    hubcapFit theRedpart rf9 p9_154l
    (Hubcap.one 0 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_188_1, c9_188_2, c9_188_3, c9_188_4, c9_188_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_153l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_153l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_190_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_153l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_190 :
    hubcapFit theRedpart rf9 p9_153l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_190_1, c9_190_2, c9_190_3, c9_190_4, c9_190_5, c9_190_6, c9_190_7, c9_190_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_152l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_152l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_152l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_152l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_152l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_192_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_152l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_192 :
    hubcapFit theRedpart rf9 p9_152l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_192_1, c9_192_2, c9_192_3, c9_192_4, c9_192_5, c9_192_6, c9_192_7, c9_192_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_151l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_151l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_151l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_151l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_151l) (hubSubn 9 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_194_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_151l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_194 :
    hubcapFit theRedpart rf9 p9_151l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 6 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_194_1, c9_194_2, c9_194_3, c9_194_4, c9_194_5, c9_194_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_150l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_150l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_150l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_150l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_150l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_150l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_195_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_150l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_195 :
    hubcapFit theRedpart rf9 p9_150l
    (Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_195_1, c9_195_2, c9_195_3, c9_195_4, c9_195_5, c9_195_6, c9_195_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_214r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_214r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_215_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_214r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_215 :
    hubcapFit theRedpart rf9 p9_214r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_215_1, c9_215_2, c9_215_3, c9_215_4, c9_215_5, c9_215_6, c9_215_7, c9_215_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_216_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_214l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_216 :
    hubcapFit theRedpart rf9 p9_214l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_216_1, c9_216_2, c9_216_3, c9_216_4, c9_216_5, c9_216_6, c9_216_7, c9_216_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_213l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_213l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_213l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_213l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_213l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_213l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_218_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_213l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_218 :
    hubcapFit theRedpart rf9 p9_213l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_218_1, c9_218_2, c9_218_3, c9_218_4, c9_218_5, c9_218_6, c9_218_7, c9_218_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_211l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_220_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_211l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_220 :
    hubcapFit theRedpart rf9 p9_211l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_220_1, c9_220_2, c9_220_3, c9_220_4, c9_220_5, c9_220_6, c9_220_7, c9_220_8, c9_220_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_210l) (hubSubn 9 4 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_210l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_222_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_210l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_222 :
    hubcapFit theRedpart rf9 p9_210l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 4 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_222_1, c9_222_2, c9_222_3, c9_222_4, c9_222_5, c9_222_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_208l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_208l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_208l) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_224_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_208l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_224 :
    hubcapFit theRedpart rf9 p9_208l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_224_1, c9_224_2, c9_224_3, c9_224_4, c9_224_5, c9_224_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_207l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_207l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_207l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_207l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_225_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_207l) (hubSubn 9 7 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_225 :
    hubcapFit theRedpart rf9 p9_207l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_225_1, c9_225_2, c9_225_3, c9_225_4, c9_225_5, c9_225_6, c9_225_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_206l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_206l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_206l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_227_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_206l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_227 :
    hubcapFit theRedpart rf9 p9_206l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_227_1, c9_227_2, c9_227_3, c9_227_4, c9_227_5, c9_227_6]

end FourColor

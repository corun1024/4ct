import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_157_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_157_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_125l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_157_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_157_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_125l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_157_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_125l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_157 :
    hubcapFit theRedpart rf7 p7_125l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_157_1, c7_157_2, c7_157_3, c7_157_4, c7_157_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_159_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_159_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_159_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_159_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_124l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_159_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_124l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_159 :
    hubcapFit theRedpart rf7 p7_124l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_159_1, c7_159_2, c7_159_3, c7_159_4, c7_159_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_187_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_186r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_187_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_186r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_187_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_186r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_187_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_186r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_187_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_186r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_187 :
    hubcapFit theRedpart rf7 p7_186r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_187_1, c7_187_2, c7_187_3, c7_187_4, c7_187_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_191r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_191r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_191r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_191r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_191r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_192_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_191r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_192 :
    hubcapFit theRedpart rf7 p7_191r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_192_1, c7_192_2, c7_192_3, c7_192_4, c7_192_5, c7_192_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_193_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_191l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_193_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_191l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_193_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_191l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_193_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_191l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_193_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_191l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_193 :
    hubcapFit theRedpart rf7 p7_191l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_193_1, c7_193_2, c7_193_3, c7_193_4, c7_193_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_195_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_195_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_195_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_195_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_189l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_195_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_189l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_195 :
    hubcapFit theRedpart rf7 p7_189l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_195_1, c7_195_2, c7_195_3, c7_195_4, c7_195_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_198_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_180l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_198_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_198_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_198_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_180l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_198_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_180l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_198 :
    hubcapFit theRedpart rf7 p7_180l
    (Hubcap.one 0 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_198_1, c7_198_2, c7_198_3, c7_198_4, c7_198_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_179l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_179l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_199_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_179l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_199 :
    hubcapFit theRedpart rf7 p7_179l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_199_1, c7_199_2, c7_199_3, c7_199_4, c7_199_5, c7_199_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_178l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_178l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_201_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_178l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_201 :
    hubcapFit theRedpart rf7 p7_178l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_201_1, c7_201_2, c7_201_3, c7_201_4, c7_201_5, c7_201_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_202_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_177l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_202_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_202_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_202_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_177l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_202_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_177l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_202 :
    hubcapFit theRedpart rf7 p7_177l
    (Hubcap.one 0 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_202_1, c7_202_2, c7_202_3, c7_202_4, c7_202_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_204_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_176l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_204_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_204_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_204_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_176l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_204_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_176l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_204 :
    hubcapFit theRedpart rf7 p7_176l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_204_1, c7_204_2, c7_204_3, c7_204_4, c7_204_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_216r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_216r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_216r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_216r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_216r) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_217_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_216r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_217 :
    hubcapFit theRedpart rf7 p7_216r
    (Hubcap.one 0 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_217_1, c7_217_2, c7_217_3, c7_217_4, c7_217_5, c7_217_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_218_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_218_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_216l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_218_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_218_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_216l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_218_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_216l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_218 :
    hubcapFit theRedpart rf7 p7_216l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_218_1, c7_218_2, c7_218_3, c7_218_4, c7_218_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_220_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_214l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_220_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_220_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_214l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_220_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_214l) (hubSubn 7 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_220_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_214l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_220 :
    hubcapFit theRedpart rf7 p7_214l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_220_1, c7_220_2, c7_220_3, c7_220_4, c7_220_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_213l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_213l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_222_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_213l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_222 :
    hubcapFit theRedpart rf7 p7_213l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_222_1, c7_222_2, c7_222_3, c7_222_4, c7_222_5, c7_222_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_223_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_212l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_223_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_223_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_212l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_223_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_212l) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_223_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_212l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_223 :
    hubcapFit theRedpart rf7 p7_212l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_223_1, c7_223_2, c7_223_3, c7_223_4, c7_223_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_225_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_211l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_225_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_211l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_225_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_211l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_225_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_211l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_225_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_211l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_225 :
    hubcapFit theRedpart rf7 p7_211l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_225_1, c7_225_2, c7_225_3, c7_225_4, c7_225_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_226_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_210l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_226_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_210l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_226_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_210l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_226_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_210l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_226 :
    hubcapFit theRedpart rf7 p7_210l
    (Hubcap.one 1 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_226_1, c7_226_2, c7_226_3, c7_226_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_208l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_208l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_208l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_208l) (hubSubn 7 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_208l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_228_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_208l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_228 :
    hubcapFit theRedpart rf7 p7_208l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_228_1, c7_228_2, c7_228_3, c7_228_4, c7_228_5, c7_228_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_230_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_207l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_230_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_207l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_230_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_230_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_207l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_230_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_207l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_230 :
    hubcapFit theRedpart rf7 p7_207l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_230_1, c7_230_2, c7_230_3, c7_230_4, c7_230_5]

end FourColor

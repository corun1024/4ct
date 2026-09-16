import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_205l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_205l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_205l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_205l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_205l) (hubSubn 9 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_228_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_205l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_228 :
    hubcapFit theRedpart rf9 p9_205l
    (Hubcap.one 5 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_228_1, c9_228_2, c9_228_3, c9_228_4, c9_228_5, c9_228_6, c9_228_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_230_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_204l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_230_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_204l) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_230_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_204l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_230_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_204l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_230_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_204l) (hubSubn 9 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_230 :
    hubcapFit theRedpart rf9 p9_204l
    (Hubcap.one 5 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_230_1, c9_230_2, c9_230_3, c9_230_4, c9_230_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_231_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_231_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_203l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_231_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_203l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_231_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_203l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_231_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_203l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_231 :
    hubcapFit theRedpart rf9 p9_203l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_231_1, c9_231_2, c9_231_3, c9_231_4, c9_231_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_202l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_202l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_202l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_202l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_233_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_202l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_233 :
    hubcapFit theRedpart rf9 p9_202l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_233_1, c9_233_2, c9_233_3, c9_233_4, c9_233_5, c9_233_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_234_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_201l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_234_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_201l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_234_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_201l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_234_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_201l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_234_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_201l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_234 :
    hubcapFit theRedpart rf9 p9_201l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_234_1, c9_234_2, c9_234_3, c9_234_4, c9_234_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_200l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_200l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_200l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_200l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_236_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_200l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_236 :
    hubcapFit theRedpart rf9 p9_200l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_236_1, c9_236_2, c9_236_3, c9_236_4, c9_236_5, c9_236_6, c9_236_7, c9_236_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_199l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_199l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_199l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_199l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_238_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_199l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_238 :
    hubcapFit theRedpart rf9 p9_199l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_238_1, c9_238_2, c9_238_3, c9_238_4, c9_238_5, c9_238_6, c9_238_7, c9_238_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_240_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_198l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_240_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_198l) (hubSubn 9 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_240_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_198l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_240_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_198l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_240_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_198l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_240 :
    hubcapFit theRedpart rf9 p9_198l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_240_1, c9_240_2, c9_240_3, c9_240_4, c9_240_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_241_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_197l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_241_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_197l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_241_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_197l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_241_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_197l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_241_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_197l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_241 :
    hubcapFit theRedpart rf9 p9_197l
    (Hubcap.one 2 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_241_1, c9_241_2, c9_241_3, c9_241_4, c9_241_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_247r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_247r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_247r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_247r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_247r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_247r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_247r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_248_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_247r) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_248 :
    hubcapFit theRedpart rf9 p9_247r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_248_1, c9_248_2, c9_248_3, c9_248_4, c9_248_5, c9_248_6, c9_248_7, c9_248_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_247l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_249_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_247l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_249 :
    hubcapFit theRedpart rf9 p9_247l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_249_1, c9_249_2, c9_249_3, c9_249_4, c9_249_5, c9_249_6, c9_249_7, c9_249_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_246l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_251_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_246l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_251 :
    hubcapFit theRedpart rf9 p9_246l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_251_1, c9_251_2, c9_251_3, c9_251_4, c9_251_5, c9_251_6, c9_251_7, c9_251_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_245l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_245l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_245l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_245l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_253_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_245l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_253 :
    hubcapFit theRedpart rf9 p9_245l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_253_1, c9_253_2, c9_253_3, c9_253_4, c9_253_5, c9_253_6, c9_253_7, c9_253_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_244l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_244l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_244l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_255_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_244l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_255 :
    hubcapFit theRedpart rf9 p9_244l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_255_1, c9_255_2, c9_255_3, c9_255_4, c9_255_5, c9_255_6, c9_255_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_263r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_263r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_263r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_263r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_263r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_263r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_263r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_264_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_263r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_264 :
    hubcapFit theRedpart rf9 p9_263r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_264_1, c9_264_2, c9_264_3, c9_264_4, c9_264_5, c9_264_6, c9_264_7, c9_264_8]

end FourColor

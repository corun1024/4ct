import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_237_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_236r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_237_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_236r) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_237_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_236r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_237_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_236r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_237 :
    hubcapFit theRedpart rf7 p7_236r
    (Hubcap.one 1 0 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_237_1, c7_237_2, c7_237_3, c7_237_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_238_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_236l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_238_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_236l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_238_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_236l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_238_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_236l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_238_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_236l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_238 :
    hubcapFit theRedpart rf7 p7_236l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_238_1, c7_238_2, c7_238_3, c7_238_4, c7_238_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_235l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_235l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_235l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_235l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_235l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_240_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_235l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_240 :
    hubcapFit theRedpart rf7 p7_235l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_240_1, c7_240_2, c7_240_3, c7_240_4, c7_240_5, c7_240_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_234l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_234l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_234l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_234l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_234l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_241_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_234l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_241 :
    hubcapFit theRedpart rf7 p7_234l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_241_1, c7_241_2, c7_241_3, c7_241_4, c7_241_5, c7_241_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_233l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_233l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_233l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_233l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_233l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_243_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_233l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_243 :
    hubcapFit theRedpart rf7 p7_233l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_243_1, c7_243_2, c7_243_3, c7_243_4, c7_243_5, c7_243_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_256r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_256r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_256r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_256r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_256r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_256r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_257_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_256r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_257 :
    hubcapFit theRedpart rf7 p7_256r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_257_1, c7_257_2, c7_257_3, c7_257_4, c7_257_5, c7_257_6, c7_257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_256l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_256l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_256l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_256l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_256l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_258_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_256l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_258 :
    hubcapFit theRedpart rf7 p7_256l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_258_1, c7_258_2, c7_258_3, c7_258_4, c7_258_5, c7_258_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_255l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_255l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_260_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_255l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_260 :
    hubcapFit theRedpart rf7 p7_255l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_260_1, c7_260_2, c7_260_3, c7_260_4, c7_260_5, c7_260_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_261_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_254l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_261_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_254l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_261_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_254l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_261_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_254l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_261_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_254l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_261 :
    hubcapFit theRedpart rf7 p7_254l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_261_1, c7_261_2, c7_261_3, c7_261_4, c7_261_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_263_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_253l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_263_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_253l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_263_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_253l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_263_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_253l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_263_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_253l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_263 :
    hubcapFit theRedpart rf7 p7_253l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_263_1, c7_263_2, c7_263_3, c7_263_4, c7_263_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_252l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_252l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_252l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_252l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_252l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_264_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_252l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_264 :
    hubcapFit theRedpart rf7 p7_252l
    (Hubcap.one 0 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_264_1, c7_264_2, c7_264_3, c7_264_4, c7_264_5, c7_264_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_266_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_251l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_266_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_251l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_266_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_251l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_266_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_251l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_266_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_251l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_266 :
    hubcapFit theRedpart rf7 p7_251l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_266_1, c7_266_2, c7_266_3, c7_266_4, c7_266_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_250l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_250l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_250l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_250l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_250l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_267_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_250l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_267 :
    hubcapFit theRedpart rf7 p7_250l
    (Hubcap.one 0 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_267_1, c7_267_2, c7_267_3, c7_267_4, c7_267_5, c7_267_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_269_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_248l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_269_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_248l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_269_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_248l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_269_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_248l) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_269_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_248l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_269 :
    hubcapFit theRedpart rf7 p7_248l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_269_1, c7_269_2, c7_269_3, c7_269_4, c7_269_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_271_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_271_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_247l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_271_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_247l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_271_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_247l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_271_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_247l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_271 :
    hubcapFit theRedpart rf7 p7_247l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_271_1, c7_271_2, c7_271_3, c7_271_4, c7_271_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_246l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_272_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_246l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_272 :
    hubcapFit theRedpart rf7 p7_246l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_272_1, c7_272_2, c7_272_3, c7_272_4, c7_272_5, c7_272_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_291r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_291r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_291r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_291r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_291r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_291r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_292_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_291r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_292 :
    hubcapFit theRedpart rf7 p7_291r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_292_1, c7_292_2, c7_292_3, c7_292_4, c7_292_5, c7_292_6, c7_292_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_291l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_291l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_291l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_291l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_291l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_293_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_291l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_293 :
    hubcapFit theRedpart rf7 p7_291l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_293_1, c7_293_2, c7_293_3, c7_293_4, c7_293_5, c7_293_6]

end FourColor

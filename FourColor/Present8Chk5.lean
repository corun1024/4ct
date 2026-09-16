import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_226l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_226l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_226l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_226l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_251_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_226l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_251 :
    hubcapFit theRedpart rf8 p8_226l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_251_1, c8_251_2, c8_251_3, c8_251_4, c8_251_5, c8_251_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_225l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_225l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_225l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_252_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_225l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_252 :
    hubcapFit theRedpart rf8 p8_225l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_252_1, c8_252_2, c8_252_3, c8_252_4, c8_252_5, c8_252_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_224l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_224l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_224l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_224l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_224l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_254_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_224l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_254 :
    hubcapFit theRedpart rf8 p8_224l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_254_1, c8_254_2, c8_254_3, c8_254_4, c8_254_5, c8_254_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_264r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_264r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_264r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_264r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_264r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_264r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_265_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_264r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_265 :
    hubcapFit theRedpart rf8 p8_264r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_265_1, c8_265_2, c8_265_3, c8_265_4, c8_265_5, c8_265_6, c8_265_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_264l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_266_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_264l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_266 :
    hubcapFit theRedpart rf8 p8_264l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_266_1, c8_266_2, c8_266_3, c8_266_4, c8_266_5, c8_266_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_268_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_263l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_268_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_268_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_263l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_268_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_263l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_268_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_263l) (hubSubn 8 7 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_268 :
    hubcapFit theRedpart rf8 p8_263l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_268_1, c8_268_2, c8_268_3, c8_268_4, c8_268_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_262l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_262l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_269_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_262l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_269 :
    hubcapFit theRedpart rf8 p8_262l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_269_1, c8_269_2, c8_269_3, c8_269_4, c8_269_5, c8_269_6, c8_269_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_261l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_261l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_271_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_261l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_271 :
    hubcapFit theRedpart rf8 p8_261l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_271_1, c8_271_2, c8_271_3, c8_271_4, c8_271_5, c8_271_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_260l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_260l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_260l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_272_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_260l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_272 :
    hubcapFit theRedpart rf8 p8_260l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_272_1, c8_272_2, c8_272_3, c8_272_4, c8_272_5, c8_272_6, c8_272_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_259l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_259l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_259l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_274_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_259l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_274 :
    hubcapFit theRedpart rf8 p8_259l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_274_1, c8_274_2, c8_274_3, c8_274_4, c8_274_5, c8_274_6, c8_274_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_258l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_276_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_276 :
    hubcapFit theRedpart rf8 p8_258l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_276_1, c8_276_2, c8_276_3, c8_276_4, c8_276_5, c8_276_6, c8_276_7, c8_276_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_257l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_257l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_278_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_257l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_278 :
    hubcapFit theRedpart rf8 p8_257l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_278_1, c8_278_2, c8_278_3, c8_278_4, c8_278_5, c8_278_6, c8_278_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_256l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_256l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_256l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_256l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_256l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_256l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_280_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_256l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_280 :
    hubcapFit theRedpart rf8 p8_256l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_280_1, c8_280_2, c8_280_3, c8_280_4, c8_280_5, c8_280_6, c8_280_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_282_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_219l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_282_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_219l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_282_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_219l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_282_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_219l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_282_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_219l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_282 :
    hubcapFit theRedpart rf8 p8_219l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_282_1, c8_282_2, c8_282_3, c8_282_4, c8_282_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_284_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_218l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_284_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_218l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_284_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_218l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_284_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_218l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_284_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_218l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_284 :
    hubcapFit theRedpart rf8 p8_218l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_284_1, c8_284_2, c8_284_3, c8_284_4, c8_284_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_293_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_292r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_293_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_292r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_293_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_292r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_293_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_292r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_293_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_292r) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_293 :
    hubcapFit theRedpart rf8 p8_292r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_293_1, c8_293_2, c8_293_3, c8_293_4, c8_293_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_294_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_292l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_294_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_292l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_294_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_292l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_294_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_292l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_294 :
    hubcapFit theRedpart rf8 p8_292l
    (Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_294_1, c8_294_2, c8_294_3, c8_294_4]

end FourColor

import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_257l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_257l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_257l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_257l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_258_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_257l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_258 :
    hubcapFit theRedpart rf10 p10_257l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_258_1, c10_258_2, c10_258_3, c10_258_4, c10_258_5, c10_258_6, c10_258_7, c10_258_8, c10_258_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_260l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_260l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_260l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_261_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_260l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_261 :
    hubcapFit theRedpart rf10 p10_260l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_261_1, c10_261_2, c10_261_3, c10_261_4, c10_261_5, c10_261_6, c10_261_7, c10_261_8, c10_261_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_260r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_260r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_260r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_260r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_260r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_260r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_260r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_260r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_263_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_260r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_263 :
    hubcapFit theRedpart rf10 p10_260r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_263_1, c10_263_2, c10_263_3, c10_263_4, c10_263_5, c10_263_6, c10_263_7, c10_263_8, c10_263_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_273l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_273l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_273l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_274_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_273l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_274 :
    hubcapFit theRedpart rf10 p10_273l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_274_1, c10_274_2, c10_274_3, c10_274_4, c10_274_5, c10_274_6, c10_274_7, c10_274_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_273r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_273r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_273r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_276_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_273r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_276 :
    hubcapFit theRedpart rf10 p10_273r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_276_1, c10_276_2, c10_276_3, c10_276_4, c10_276_5, c10_276_6, c10_276_7, c10_276_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_279l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_280_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_279l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_280 :
    hubcapFit theRedpart rf10 p10_279l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_280_1, c10_280_2, c10_280_3, c10_280_4, c10_280_5, c10_280_6, c10_280_7, c10_280_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_279r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_279r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_279r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_279r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_279r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_279r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_279r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_282_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_279r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_282 :
    hubcapFit theRedpart rf10 p10_279r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_282_1, c10_282_2, c10_282_3, c10_282_4, c10_282_5, c10_282_6, c10_282_7, c10_282_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_286l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_287_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_286l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_287 :
    hubcapFit theRedpart rf10 p10_286l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_287_1, c10_287_2, c10_287_3, c10_287_4, c10_287_5, c10_287_6, c10_287_7, c10_287_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_286r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_286r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_286r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_289_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_286r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_289 :
    hubcapFit theRedpart rf10 p10_286r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_289_1, c10_289_2, c10_289_3, c10_289_4, c10_289_5, c10_289_6, c10_289_7, c10_289_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_293l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_293l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_293l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_293l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_294_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_293l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_294 :
    hubcapFit theRedpart rf10 p10_293l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_294_1, c10_294_2, c10_294_3, c10_294_4, c10_294_5, c10_294_6, c10_294_7, c10_294_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_293r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_293r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_293r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_293r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_293r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_293r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_293r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_296_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_293r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_296 :
    hubcapFit theRedpart rf10 p10_293r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_296_1, c10_296_2, c10_296_3, c10_296_4, c10_296_5, c10_296_6, c10_296_7, c10_296_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_300l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_301_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_300l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_301 :
    hubcapFit theRedpart rf10 p10_300l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_301_1, c10_301_2, c10_301_3, c10_301_4, c10_301_5, c10_301_6, c10_301_7, c10_301_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_300r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_300r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_300r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_303_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_300r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_303 :
    hubcapFit theRedpart rf10 p10_300r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_303_1, c10_303_2, c10_303_3, c10_303_4, c10_303_5, c10_303_6, c10_303_7, c10_303_8]

end FourColor

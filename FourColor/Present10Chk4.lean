import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_198l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_198l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_198l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_198l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_212_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_198l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_212 :
    hubcapFit theRedpart rf10 p10_198l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_212_1, c10_212_2, c10_212_3, c10_212_4, c10_212_5, c10_212_6, c10_212_7, c10_212_8, c10_212_9, c10_212_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_197l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_197l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_197l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_215_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_215 :
    hubcapFit theRedpart rf10 p10_197l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_215_1, c10_215_2, c10_215_3, c10_215_4, c10_215_5, c10_215_6, c10_215_7, c10_215_8, c10_215_9, c10_215_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_196l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_196l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_196l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_196l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_196l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_196l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_196l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_196l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_196l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_217_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_196l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_217 :
    hubcapFit theRedpart rf10 p10_196l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_217_1, c10_217_2, c10_217_3, c10_217_4, c10_217_5, c10_217_6, c10_217_7, c10_217_8, c10_217_9, c10_217_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_195l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_195l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_195l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_219_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_195l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_219 :
    hubcapFit theRedpart rf10 p10_195l
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
  simp [hubcapFit, c10_219_1, c10_219_2, c10_219_3, c10_219_4, c10_219_5, c10_219_6, c10_219_7, c10_219_8, c10_219_9, c10_219_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_148l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_148l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_148l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_148l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_222_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_148l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_222 :
    hubcapFit theRedpart rf10 p10_148l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_222_1, c10_222_2, c10_222_3, c10_222_4, c10_222_5, c10_222_6, c10_222_7, c10_222_8, c10_222_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_100l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_100l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_100l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_100l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_100l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_100l) (hubSubn 10 6 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_225_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_100l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_225 :
    hubcapFit theRedpart rf10 p10_100l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_225_1, c10_225_2, c10_225_3, c10_225_4, c10_225_5, c10_225_6, c10_225_7, c10_225_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_99l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_99l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_99l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_99l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_99l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_99l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_99l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_99l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_227_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_99l) (hubSubn 10 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_227 :
    hubcapFit theRedpart rf10 p10_99l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_227_1, c10_227_2, c10_227_3, c10_227_4, c10_227_5, c10_227_6, c10_227_7, c10_227_8, c10_227_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_98l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_98l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_98l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_98l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_98l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_98l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_98l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_98l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_229_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_98l) (hubSubn 10 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_229 :
    hubcapFit theRedpart rf10 p10_98l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_229_1, c10_229_2, c10_229_3, c10_229_4, c10_229_5, c10_229_6, c10_229_7, c10_229_8, c10_229_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_97l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_97l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_97l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_97l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_97l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_97l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_97l) (hubSubn 10 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_231_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_97l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_231 :
    hubcapFit theRedpart rf10 p10_97l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_231_1, c10_231_2, c10_231_3, c10_231_4, c10_231_5, c10_231_6, c10_231_7, c10_231_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_96l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_96l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_96l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_96l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_96l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_96l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_96l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_96l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_233_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_96l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_233 :
    hubcapFit theRedpart rf10 p10_96l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_233_1, c10_233_2, c10_233_3, c10_233_4, c10_233_5, c10_233_6, c10_233_7, c10_233_8, c10_233_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_241r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_242_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_241r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_242 :
    hubcapFit theRedpart rf10 p10_241r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_242_1, c10_242_2, c10_242_3, c10_242_4, c10_242_5, c10_242_6, c10_242_7, c10_242_8, c10_242_9, c10_242_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_252r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_252r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_252r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_252r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_252r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_252r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_252r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_252r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_252r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_253_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_252r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_253 :
    hubcapFit theRedpart rf10 p10_252r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_253_1, c10_253_2, c10_253_3, c10_253_4, c10_253_5, c10_253_6, c10_253_7, c10_253_8, c10_253_9, c10_253_10]

end FourColor

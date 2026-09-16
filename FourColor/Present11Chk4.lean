import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_219_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_219 :
    hubcapFit theRedpart rf11 p11_217l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_219_1, c11_219_2, c11_219_3, c11_219_4, c11_219_5, c11_219_6, c11_219_7, c11_219_8, c11_219_9, c11_219_10, c11_219_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_214l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_222_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_222 :
    hubcapFit theRedpart rf11 p11_214l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_222_1, c11_222_2, c11_222_3, c11_222_4, c11_222_5, c11_222_6, c11_222_7, c11_222_8, c11_222_9, c11_222_10, c11_222_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_225_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_225 :
    hubcapFit theRedpart rf11 p11_203l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_225_1, c11_225_2, c11_225_3, c11_225_4, c11_225_5, c11_225_6, c11_225_7, c11_225_8, c11_225_9, c11_225_10, c11_225_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_201l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_201l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_201l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_201l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_201l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_227_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_201l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_227 :
    hubcapFit theRedpart rf11 p11_201l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_227_1, c11_227_2, c11_227_3, c11_227_4, c11_227_5, c11_227_6, c11_227_7, c11_227_8, c11_227_9, c11_227_10, c11_227_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_199l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_230_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_199l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_230 :
    hubcapFit theRedpart rf11 p11_199l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_230_1, c11_230_2, c11_230_3, c11_230_4, c11_230_5, c11_230_6, c11_230_7, c11_230_8, c11_230_9, c11_230_10, c11_230_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_197l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_232_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_197l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_232 :
    hubcapFit theRedpart rf11 p11_197l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_232_1, c11_232_2, c11_232_3, c11_232_4, c11_232_5, c11_232_6, c11_232_7, c11_232_8, c11_232_9, c11_232_10, c11_232_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_8 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_243l) (hubSubn 11 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_244_9 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 7 p11_243l) (hubSubn 11 8 7) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_244 :
    hubcapFit theRedpart rf11 p11_243l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_244_1, c11_244_2, c11_244_3, c11_244_4, c11_244_5, c11_244_6, c11_244_7, c11_244_8, c11_244_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_243r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_243r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_8 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_243r) (hubSubn 11 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_246_9 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 7 p11_243r) (hubSubn 11 8 7) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_246 :
    hubcapFit theRedpart rf11 p11_243r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_246_1, c11_246_2, c11_246_3, c11_246_4, c11_246_5, c11_246_6, c11_246_7, c11_246_8, c11_246_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_242l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_242l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_242l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_249_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_242l) (hubSubn 11 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_249 :
    hubcapFit theRedpart rf11 p11_242l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_249_1, c11_249_2, c11_249_3, c11_249_4, c11_249_5, c11_249_6, c11_249_7, c11_249_8, c11_249_9, c11_249_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_241l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_241l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_241l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_241l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_251_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_241l) (hubSubn 11 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_251 :
    hubcapFit theRedpart rf11 p11_241l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_251_1, c11_251_2, c11_251_3, c11_251_4, c11_251_5, c11_251_6, c11_251_7, c11_251_8, c11_251_9, c11_251_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_240l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_240l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_240l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_240l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_240l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_8 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 0 p11_240l) (hubSubn 11 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_253_9 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 4 p11_240l) (hubSubn 11 5 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_253 :
    hubcapFit theRedpart rf11 p11_240l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 4 5 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_253_1, c11_253_2, c11_253_3, c11_253_4, c11_253_5, c11_253_6, c11_253_7, c11_253_8, c11_253_9]

end FourColor

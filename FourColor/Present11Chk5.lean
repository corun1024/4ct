import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_239l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_255_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_255 :
    hubcapFit theRedpart rf11 p11_239l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_255_1, c11_255_2, c11_255_3, c11_255_4, c11_255_5, c11_255_6, c11_255_7, c11_255_8, c11_255_9, c11_255_10, c11_255_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_275r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_275r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_275r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_275r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_275r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_275r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_275r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_8 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 6 p11_275r) (hubSubn 11 7 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_276_9 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 8 p11_275r) (hubSubn 11 9 8) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_276 :
    hubcapFit theRedpart rf11 p11_275r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 7 9 <|
     Hubcap.two 8 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_276_1, c11_276_2, c11_276_3, c11_276_4, c11_276_5, c11_276_6, c11_276_7, c11_276_8, c11_276_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_275l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_275l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_275l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_275l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_275l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_275l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_275l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_275l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_275l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_277_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 7 p11_275l) (hubSubn 11 8 7) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_277 :
    hubcapFit theRedpart rf11 p11_275l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_277_1, c11_277_2, c11_277_3, c11_277_4, c11_277_5, c11_277_6, c11_277_7, c11_277_8, c11_277_9, c11_277_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_274l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_274l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_274l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_274l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_274l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_280_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 6 p11_274l) (hubSubn 11 7 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_280 :
    hubcapFit theRedpart rf11 p11_274l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 7 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_280_1, c11_280_2, c11_280_3, c11_280_4, c11_280_5, c11_280_6, c11_280_7, c11_280_8, c11_280_9, c11_280_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_273l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_273l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_273l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_273l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_273l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_282_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 5 p11_273l) (hubSubn 11 6 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_282 :
    hubcapFit theRedpart rf11 p11_273l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_282_1, c11_282_2, c11_282_3, c11_282_4, c11_282_5, c11_282_6, c11_282_7, c11_282_8, c11_282_9, c11_282_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_284_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 4 p11_272l) (hubSubn 11 5 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_284 :
    hubcapFit theRedpart rf11 p11_272l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 4 5 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_284_1, c11_284_2, c11_284_3, c11_284_4, c11_284_5, c11_284_6, c11_284_7, c11_284_8, c11_284_9, c11_284_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_271l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_271l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_271l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_271l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_286_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 3 p11_271l) (hubSubn 11 4 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_286 :
    hubcapFit theRedpart rf11 p11_271l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 3 4 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_286_1, c11_286_2, c11_286_3, c11_286_4, c11_286_5, c11_286_6, c11_286_7, c11_286_8, c11_286_9, c11_286_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_290r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_290r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_290r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_290r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_290r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_291_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_290r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_291 :
    hubcapFit theRedpart rf11 p11_290r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_291_1, c11_291_2, c11_291_3, c11_291_4, c11_291_5, c11_291_6, c11_291_7, c11_291_8, c11_291_9, c11_291_10, c11_291_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_297r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_297r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_297r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_297r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_297r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_298_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_298 :
    hubcapFit theRedpart rf11 p11_297r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_298_1, c11_298_2, c11_298_3, c11_298_4, c11_298_5, c11_298_6, c11_298_7, c11_298_8, c11_298_9, c11_298_10, c11_298_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_303r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_303r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_303r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_303r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_303r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_304_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_303r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_304 :
    hubcapFit theRedpart rf11 p11_303r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_304_1, c11_304_2, c11_304_3, c11_304_4, c11_304_5, c11_304_6, c11_304_7, c11_304_8, c11_304_9, c11_304_10, c11_304_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_307r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_307r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_308_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_308 :
    hubcapFit theRedpart rf11 p11_307r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_308_1, c11_308_2, c11_308_3, c11_308_4, c11_308_5, c11_308_6, c11_308_7, c11_308_8, c11_308_9, c11_308_10, c11_308_11]

end FourColor

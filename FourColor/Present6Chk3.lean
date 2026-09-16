import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_205_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_203l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_205_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_203l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_205_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_203l) (hubSubn 6 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_205 :
    hubcapFit theRedpart rf6 p6_203l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_205_1, c6_205_2, c6_205_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_207_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_202l) (hubSubn 6 5 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_207_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_202l) (hubSubn 6 3 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_207_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_202l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_207 :
    hubcapFit theRedpart rf6 p6_202l
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_207_1, c6_207_2, c6_207_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_209_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_194l) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_209_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_194l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_209_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_194l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_209 :
    hubcapFit theRedpart rf6 p6_194l
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_209_1, c6_209_2, c6_209_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_236_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_235r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_236_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_235r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_236_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_235r) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_236 :
    hubcapFit theRedpart rf6 p6_235r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_236_1, c6_236_2, c6_236_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_237_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_235l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_237_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_235l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_237_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_235l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_237 :
    hubcapFit theRedpart rf6 p6_235l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_237_1, c6_237_2, c6_237_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_240_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_239r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_240_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_239r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_240_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_239r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_240 :
    hubcapFit theRedpart rf6 p6_239r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_240_1, c6_240_2, c6_240_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_241_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_239l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_241_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_239l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_241_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_239l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_241 :
    hubcapFit theRedpart rf6 p6_239l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_241_1, c6_241_2, c6_241_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_243_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_233l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_243_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_233l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_243_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_233l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_243 :
    hubcapFit theRedpart rf6 p6_233l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_243_1, c6_243_2, c6_243_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_246_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_245r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_246_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_245r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_246_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_245r) (hubSubn 6 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_246 :
    hubcapFit theRedpart rf6 p6_245r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_246_1, c6_246_2, c6_246_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_247_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_245l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_247_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_245l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_247_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_245l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_247 :
    hubcapFit theRedpart rf6 p6_245l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_247_1, c6_247_2, c6_247_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_255_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_254r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_255_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_254r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_255_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_254r) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_255 :
    hubcapFit theRedpart rf6 p6_254r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_255_1, c6_255_2, c6_255_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_256_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_254l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_256_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_254l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_256_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_254l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_256 :
    hubcapFit theRedpart rf6 p6_254l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_256_1, c6_256_2, c6_256_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_259_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_258r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_259_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_258r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_259_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_258r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_259 :
    hubcapFit theRedpart rf6 p6_258r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_259_1, c6_259_2, c6_259_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_260_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_258l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_260_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_258l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_260_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_258l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_260 :
    hubcapFit theRedpart rf6 p6_258l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_260_1, c6_260_2, c6_260_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_262_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_252l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_262_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_252l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_262_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_252l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_262 :
    hubcapFit theRedpart rf6 p6_252l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_262_1, c6_262_2, c6_262_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_264_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_263r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_264_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_263r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_264_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_263r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_264 :
    hubcapFit theRedpart rf6 p6_263r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_264_1, c6_264_2, c6_264_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_265_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_263l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_265_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_263l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_265_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_263l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_265 :
    hubcapFit theRedpart rf6 p6_263l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_265_1, c6_265_2, c6_265_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_270_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_269r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_270_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_269r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_270_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_269r) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_270 :
    hubcapFit theRedpart rf6 p6_269r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_270_1, c6_270_2, c6_270_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_271_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_269l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_271_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_269l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_271_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_269l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_271 :
    hubcapFit theRedpart rf6 p6_269l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_271_1, c6_271_2, c6_271_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_274_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_273r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_274_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_273r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_274_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_273r) (hubSubn 6 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_274 :
    hubcapFit theRedpart rf6 p6_273r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_274_1, c6_274_2, c6_274_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_275_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_273l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_275_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_273l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_275_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_273l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_275 :
    hubcapFit theRedpart rf6 p6_273l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_275_1, c6_275_2, c6_275_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_283_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_282r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_283_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_282r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_283_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_282r) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_283 :
    hubcapFit theRedpart rf6 p6_282r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_283_1, c6_283_2, c6_283_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_284_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_282l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_284_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_282l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_284_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_282l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_284 :
    hubcapFit theRedpart rf6 p6_282l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_284_1, c6_284_2, c6_284_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_287_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_286r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_287_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_286r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_287_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_286r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_287 :
    hubcapFit theRedpart rf6 p6_286r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_287_1, c6_287_2, c6_287_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_288_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_286l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_288_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_286l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_288_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_286l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_288 :
    hubcapFit theRedpart rf6 p6_286l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_288_1, c6_288_2, c6_288_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_290_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_280l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_290_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_280l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_290_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_280l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_290 :
    hubcapFit theRedpart rf6 p6_280l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_290_1, c6_290_2, c6_290_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_291_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_279l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_291_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_279l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_291_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_279l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_291 :
    hubcapFit theRedpart rf6 p6_279l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_291_1, c6_291_2, c6_291_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_293_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_277l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_293_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_277l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_293_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_277l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_293 :
    hubcapFit theRedpart rf6 p6_277l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_293_1, c6_293_2, c6_293_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_302_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_301r) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_302_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_301r) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_302_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_301r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_302 :
    hubcapFit theRedpart rf6 p6_301r
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_302_1, c6_302_2, c6_302_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_303_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_301l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_303_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_301l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_303_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_301l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_303 :
    hubcapFit theRedpart rf6 p6_301l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_303_1, c6_303_2, c6_303_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_305_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_300l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_305_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_300l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_305_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_300l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_305 :
    hubcapFit theRedpart rf6 p6_300l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_305_1, c6_305_2, c6_305_3]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_263l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_263l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_263l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_263l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_263l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_265_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_265 :
    hubcapFit theRedpart rf9 p9_263l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_265_1, c9_265_2, c9_265_3, c9_265_4, c9_265_5, c9_265_6, c9_265_7, c9_265_8, c9_265_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_261l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_261l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_267_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_261l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_267 :
    hubcapFit theRedpart rf9 p9_261l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_267_1, c9_267_2, c9_267_3, c9_267_4, c9_267_5, c9_267_6, c9_267_7, c9_267_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_260l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_260l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_269_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_260l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_269 :
    hubcapFit theRedpart rf9 p9_260l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_269_1, c9_269_2, c9_269_3, c9_269_4, c9_269_5, c9_269_6, c9_269_7, c9_269_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_259l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_259l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_259l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_271_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_259l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_271 :
    hubcapFit theRedpart rf9 p9_259l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_271_1, c9_271_2, c9_271_3, c9_271_4, c9_271_5, c9_271_6, c9_271_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_258l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_258l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_258l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_273_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_258l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_273 :
    hubcapFit theRedpart rf9 p9_258l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_273_1, c9_273_2, c9_273_3, c9_273_4, c9_273_5, c9_273_6, c9_273_7, c9_273_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_276_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_276_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_146l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_276_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_146l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_276_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_146l) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_276_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_146l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_276 :
    hubcapFit theRedpart rf9 p9_146l
    (Hubcap.one 2 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_276_1, c9_276_2, c9_276_3, c9_276_4, c9_276_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_285r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_285r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_285r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_285r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_285r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_285r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_285r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_286_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_285r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_286 :
    hubcapFit theRedpart rf9 p9_285r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_286_1, c9_286_2, c9_286_3, c9_286_4, c9_286_5, c9_286_6, c9_286_7, c9_286_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_285l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_285l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_285l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_285l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_287_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_285l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_287 :
    hubcapFit theRedpart rf9 p9_285l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_287_1, c9_287_2, c9_287_3, c9_287_4, c9_287_5, c9_287_6, c9_287_7, c9_287_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_284l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_284l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_284l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_289_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_284l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_289 :
    hubcapFit theRedpart rf9 p9_284l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_289_1, c9_289_2, c9_289_3, c9_289_4, c9_289_5, c9_289_6, c9_289_7, c9_289_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_282l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_282l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_291_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_282l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_291 :
    hubcapFit theRedpart rf9 p9_282l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_291_1, c9_291_2, c9_291_3, c9_291_4, c9_291_5, c9_291_6, c9_291_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_281l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_281l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_281l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_293_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_281l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_293 :
    hubcapFit theRedpart rf9 p9_281l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_293_1, c9_293_2, c9_293_3, c9_293_4, c9_293_5, c9_293_6, c9_293_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_280l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_280l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_280l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_280l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_295_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_280l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_295 :
    hubcapFit theRedpart rf9 p9_280l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_295_1, c9_295_2, c9_295_3, c9_295_4, c9_295_5, c9_295_6, c9_295_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_279l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_279l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_279l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_279l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_297_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_279l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_297 :
    hubcapFit theRedpart rf9 p9_279l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_297_1, c9_297_2, c9_297_3, c9_297_4, c9_297_5, c9_297_6, c9_297_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_278l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_278l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_278l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_278l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_299_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_278l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_299 :
    hubcapFit theRedpart rf9 p9_278l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_299_1, c9_299_2, c9_299_3, c9_299_4, c9_299_5, c9_299_6, c9_299_7]

end FourColor

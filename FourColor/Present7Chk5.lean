import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_289l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_289l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_289l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_289l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_289l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_295_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_289l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_295 :
    hubcapFit theRedpart rf7 p7_289l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_295_1, c7_295_2, c7_295_3, c7_295_4, c7_295_5, c7_295_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_288l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_288l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_288l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_288l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_288l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_297_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_288l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_297 :
    hubcapFit theRedpart rf7 p7_288l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_297_1, c7_297_2, c7_297_3, c7_297_4, c7_297_5, c7_297_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_299_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_285l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_299_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_285l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_299_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_299_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_285l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_299_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_285l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_299 :
    hubcapFit theRedpart rf7 p7_285l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_299_1, c7_299_2, c7_299_3, c7_299_4, c7_299_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_283l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_283l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_283l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_301_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_283l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_301 :
    hubcapFit theRedpart rf7 p7_283l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_301_1, c7_301_2, c7_301_3, c7_301_4, c7_301_5, c7_301_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_303_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_303_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_282l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_303_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_282l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_303_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_282l) (hubSubn 7 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_303_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_282l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_303 :
    hubcapFit theRedpart rf7 p7_282l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_303_1, c7_303_2, c7_303_3, c7_303_4, c7_303_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_281l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_281l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_281l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_281l) (hubSubn 7 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_281l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_304_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_281l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_304 :
    hubcapFit theRedpart rf7 p7_281l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 5 4 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_304_1, c7_304_2, c7_304_3, c7_304_4, c7_304_5, c7_304_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_306_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_306_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_279l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_306_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_306_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_279l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_306_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_279l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_306 :
    hubcapFit theRedpart rf7 p7_279l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_306_1, c7_306_2, c7_306_3, c7_306_4, c7_306_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_308_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_278l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_308_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_278l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_308_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_278l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_308_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_278l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_308_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_278l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_308 :
    hubcapFit theRedpart rf7 p7_278l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_308_1, c7_308_2, c7_308_3, c7_308_4, c7_308_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_277l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_277l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_277l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_277l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_277l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_309_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_277l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_309 :
    hubcapFit theRedpart rf7 p7_277l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_309_1, c7_309_2, c7_309_3, c7_309_4, c7_309_5, c7_309_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_162l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_162l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_162l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_162l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_162l) (hubSubn 7 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_311_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_162l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_311 :
    hubcapFit theRedpart rf7 p7_162l
    (Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_311_1, c7_311_2, c7_311_3, c7_311_4, c7_311_5, c7_311_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_161l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_161l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_161l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_313_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_161l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_313 :
    hubcapFit theRedpart rf7 p7_161l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_313_1, c7_313_2, c7_313_3, c7_313_4, c7_313_5, c7_313_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_331r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_331r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_331r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_331r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_331r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_332_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_331r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_332 :
    hubcapFit theRedpart rf7 p7_331r
    (Hubcap.one 0 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_332_1, c7_332_2, c7_332_3, c7_332_4, c7_332_5, c7_332_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_333_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_333_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_333_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_333_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_331l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_333_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_331l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_333 :
    hubcapFit theRedpart rf7 p7_331l
    (Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_333_1, c7_333_2, c7_333_3, c7_333_4, c7_333_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_351r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_351r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_351r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_351r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_352_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_351r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_352 :
    hubcapFit theRedpart rf7 p7_351r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_352_1, c7_352_2, c7_352_3, c7_352_4, c7_352_5, c7_352_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_353_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_353_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_351l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_353_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_353_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_351l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_353_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_351l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_353 :
    hubcapFit theRedpart rf7 p7_351l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_353_1, c7_353_2, c7_353_3, c7_353_4, c7_353_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_355_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_355_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_355_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_355_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_349l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_355_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_349l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_355 :
    hubcapFit theRedpart rf7 p7_349l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_355_1, c7_355_2, c7_355_3, c7_355_4, c7_355_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_348l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_348l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_348l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_357_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_348l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_357 :
    hubcapFit theRedpart rf7 p7_348l
    (Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_357_1, c7_357_2, c7_357_3, c7_357_4, c7_357_5, c7_357_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_363r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_363r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_363r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_364_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_364 :
    hubcapFit theRedpart rf7 p7_363r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_364_1, c7_364_2, c7_364_3, c7_364_4, c7_364_5, c7_364_6, c7_364_7]

end FourColor

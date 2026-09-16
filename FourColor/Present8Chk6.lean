import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_296_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_296_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_296_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_291l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_296_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_291l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_296_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_291l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_296 :
    hubcapFit theRedpart rf8 p8_291l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_296_1, c8_296_2, c8_296_3, c8_296_4, c8_296_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_290l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_290l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_290l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_297_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_290l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_297 :
    hubcapFit theRedpart rf8 p8_290l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_297_1, c8_297_2, c8_297_3, c8_297_4, c8_297_5, c8_297_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_299_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_289l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_299_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_289l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_299_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_289l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_299_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_289l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_299_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_289l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_299 :
    hubcapFit theRedpart rf8 p8_289l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_299_1, c8_299_2, c8_299_3, c8_299_4, c8_299_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_301_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_287l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_301_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_287l) (hubSubn 8 7 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_301_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_287l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_301_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_287l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_301 :
    hubcapFit theRedpart rf8 p8_287l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 2 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_301_1, c8_301_2, c8_301_3, c8_301_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_302_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_286l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_302_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_286l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_302_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_286l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_302_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_286l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_302 :
    hubcapFit theRedpart rf8 p8_286l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_302_1, c8_302_2, c8_302_3, c8_302_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_133l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_133l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_133l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_133l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_304_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_133l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_304 :
    hubcapFit theRedpart rf8 p8_133l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_304_1, c8_304_2, c8_304_3, c8_304_4, c8_304_5, c8_304_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_323r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_323r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_323r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_323r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_323r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_324_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_323r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_324 :
    hubcapFit theRedpart rf8 p8_323r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_324_1, c8_324_2, c8_324_3, c8_324_4, c8_324_5, c8_324_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_323l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_323l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_323l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_325_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_323l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_325 :
    hubcapFit theRedpart rf8 p8_323l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_325_1, c8_325_2, c8_325_3, c8_325_4, c8_325_5, c8_325_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_322l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_322l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_322l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_322l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_327_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_322l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_327 :
    hubcapFit theRedpart rf8 p8_322l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_327_1, c8_327_2, c8_327_3, c8_327_4, c8_327_5, c8_327_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_321l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_321l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_321l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_321l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_321l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_328_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_321l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_328 :
    hubcapFit theRedpart rf8 p8_321l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_328_1, c8_328_2, c8_328_3, c8_328_4, c8_328_5, c8_328_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_320l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_320l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_320l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_320l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_320l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_330_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_320l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_330 :
    hubcapFit theRedpart rf8 p8_320l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_330_1, c8_330_2, c8_330_3, c8_330_4, c8_330_5, c8_330_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_332_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_318l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_332_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_318l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_332_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_318l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_332_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_318l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_332_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_318l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_332 :
    hubcapFit theRedpart rf8 p8_318l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_332_1, c8_332_2, c8_332_3, c8_332_4, c8_332_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_333_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_333_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_333_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_317l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_333_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_317l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_333_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_317l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_333 :
    hubcapFit theRedpart rf8 p8_317l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_333_1, c8_333_2, c8_333_3, c8_333_4, c8_333_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_344r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_344r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_344r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_344r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_344r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_344r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_345_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_344r) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_345 :
    hubcapFit theRedpart rf8 p8_344r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_345_1, c8_345_2, c8_345_3, c8_345_4, c8_345_5, c8_345_6, c8_345_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_344l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_344l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_344l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_344l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_346_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_344l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_346 :
    hubcapFit theRedpart rf8 p8_344l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_346_1, c8_346_2, c8_346_3, c8_346_4, c8_346_5, c8_346_6, c8_346_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_343l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_343l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_343l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_343l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_343l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_343l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_348_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_343l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_348 :
    hubcapFit theRedpart rf8 p8_343l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_348_1, c8_348_2, c8_348_3, c8_348_4, c8_348_5, c8_348_6, c8_348_7, c8_348_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_342l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_342l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_342l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_342l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_342l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_350_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_342l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_350 :
    hubcapFit theRedpart rf8 p8_342l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_350_1, c8_350_2, c8_350_3, c8_350_4, c8_350_5, c8_350_6, c8_350_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_341l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_341l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_341l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_341l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_341l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_341l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_352_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_341l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_352 :
    hubcapFit theRedpart rf8 p8_341l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_352_1, c8_352_2, c8_352_3, c8_352_4, c8_352_5, c8_352_6, c8_352_7]

end FourColor

import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_306_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_298l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_306_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_298l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_306_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_298l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_306 :
    hubcapFit theRedpart rf6 p6_298l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_306_1, c6_306_2, c6_306_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_312_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_311r) (hubSubn 6 4 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_312_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_311r) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_312_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_311r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_312 :
    hubcapFit theRedpart rf6 p6_311r
    (Hubcap.two 0 4 (-3) <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_312_1, c6_312_2, c6_312_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_313_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_311l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_313_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_311l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_313_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_311l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_313 :
    hubcapFit theRedpart rf6 p6_311l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_313_1, c6_313_2, c6_313_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_315_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_310l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_315_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_310l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_315_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_310l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_315 :
    hubcapFit theRedpart rf6 p6_310l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_315_1, c6_315_2, c6_315_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_316_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_308l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_316_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_308l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_316_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_308l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_316 :
    hubcapFit theRedpart rf6 p6_308l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_316_1, c6_316_2, c6_316_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_319_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_318r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_319_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_318r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_319_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_318r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_319 :
    hubcapFit theRedpart rf6 p6_318r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_319_1, c6_319_2, c6_319_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_320_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_318l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_320_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_318l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_320_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_318l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_320 :
    hubcapFit theRedpart rf6 p6_318l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_320_1, c6_320_2, c6_320_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_328_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_327r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_328_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_327r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_328_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_327r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_328 :
    hubcapFit theRedpart rf6 p6_327r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_328_1, c6_328_2, c6_328_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_329_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_327l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_329_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_327l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_329_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_327l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_329 :
    hubcapFit theRedpart rf6 p6_327l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_329_1, c6_329_2, c6_329_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_331_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_326l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_331_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_326l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_331_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_326l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_331 :
    hubcapFit theRedpart rf6 p6_326l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_331_1, c6_331_2, c6_331_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_335_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_334r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_335_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_334r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_335_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_334r) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_335 :
    hubcapFit theRedpart rf6 p6_334r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_335_1, c6_335_2, c6_335_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_336_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_334l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_336_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_334l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_336_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_334l) (hubSubn 6 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_336 :
    hubcapFit theRedpart rf6 p6_334l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_336_1, c6_336_2, c6_336_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_338_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_333l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_338_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_333l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_338_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_333l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_338 :
    hubcapFit theRedpart rf6 p6_333l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_338_1, c6_338_2, c6_338_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_340_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_323l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_340_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_323l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_340_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_323l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_340 :
    hubcapFit theRedpart rf6 p6_323l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_340_1, c6_340_2, c6_340_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_343_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_342r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_343_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_342r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_343_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_342r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_343 :
    hubcapFit theRedpart rf6 p6_342r
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_343_1, c6_343_2, c6_343_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_344_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_342l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_344_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_342l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_344_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_342l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_344 :
    hubcapFit theRedpart rf6 p6_342l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_344_1, c6_344_2, c6_344_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_349_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_348r) (hubSubn 6 2 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_349_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_348r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_349_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_348r) (hubSubn 6 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_349 :
    hubcapFit theRedpart rf6 p6_348r
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_349_1, c6_349_2, c6_349_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_350_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_348l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_350_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_348l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_350_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_348l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_350 :
    hubcapFit theRedpart rf6 p6_348l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_350_1, c6_350_2, c6_350_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_352_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_347l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_352_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_347l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_352_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_347l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_352 :
    hubcapFit theRedpart rf6 p6_347l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_352_1, c6_352_2, c6_352_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_364_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_363r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_364_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_363r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_364_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_363r) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_364 :
    hubcapFit theRedpart rf6 p6_363r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_364_1, c6_364_2, c6_364_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_365_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_363l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_365_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_363l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_365_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_363l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_365 :
    hubcapFit theRedpart rf6 p6_363l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_365_1, c6_365_2, c6_365_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_367_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_361l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_367_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_361l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_367_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_361l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_367 :
    hubcapFit theRedpart rf6 p6_361l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_367_1, c6_367_2, c6_367_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_368_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_360l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_368_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_360l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_368_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_360l) (hubSubn 6 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_368 :
    hubcapFit theRedpart rf6 p6_360l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_368_1, c6_368_2, c6_368_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_370_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_359l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_370_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_359l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_370_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_359l) (hubSubn 6 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_370 :
    hubcapFit theRedpart rf6 p6_359l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_370_1, c6_370_2, c6_370_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_371_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_358l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_371_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_358l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_371_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_358l) (hubSubn 6 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_371 :
    hubcapFit theRedpart rf6 p6_358l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_371_1, c6_371_2, c6_371_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_389_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_388r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_389_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_388r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_389_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_388r) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_389 :
    hubcapFit theRedpart rf6 p6_388r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_389_1, c6_389_2, c6_389_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_390_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_388l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_390_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_388l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_390_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_388l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_390 :
    hubcapFit theRedpart rf6 p6_388l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_390_1, c6_390_2, c6_390_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_393_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_392r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_393_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_392r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_393_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_392r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_393 :
    hubcapFit theRedpart rf6 p6_392r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_393_1, c6_393_2, c6_393_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_394_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_392l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_394_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_392l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_394_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_392l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_394 :
    hubcapFit theRedpart rf6 p6_392l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_394_1, c6_394_2, c6_394_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_396_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_386l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_396_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_386l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_396_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_386l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_396 :
    hubcapFit theRedpart rf6 p6_386l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_396_1, c6_396_2, c6_396_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_402_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_401r) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_402_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_401r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_402_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_401r) (hubSubn 6 2 1) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_402 :
    hubcapFit theRedpart rf6 p6_401r
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_402_1, c6_402_2, c6_402_3]

end FourColor

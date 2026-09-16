import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 7 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_143l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_143l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_301_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_143l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_301 :
    hubcapFit theRedpart rf9 p9_143l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 0 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_301_1, c9_301_2, c9_301_3, c9_301_4, c9_301_5, c9_301_6, c9_301_7, c9_301_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_142l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_142l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_142l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_142l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_142l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_303_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_142l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_303 :
    hubcapFit theRedpart rf9 p9_142l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_303_1, c9_303_2, c9_303_3, c9_303_4, c9_303_5, c9_303_6, c9_303_7, c9_303_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_141l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_141l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_141l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_141l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_141l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_141l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_141l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_305_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_141l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_305 :
    hubcapFit theRedpart rf9 p9_141l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_305_1, c9_305_2, c9_305_3, c9_305_4, c9_305_5, c9_305_6, c9_305_7, c9_305_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_140l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_140l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_140l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_140l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_140l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_307_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_140l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_307 :
    hubcapFit theRedpart rf9 p9_140l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_307_1, c9_307_2, c9_307_3, c9_307_4, c9_307_5, c9_307_6, c9_307_7, c9_307_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_139l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_139l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_139l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_139l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_139l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_139l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_139l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_309_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_139l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_309 :
    hubcapFit theRedpart rf9 p9_139l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_309_1, c9_309_2, c9_309_3, c9_309_4, c9_309_5, c9_309_6, c9_309_7, c9_309_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_138l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_138l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_138l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_138l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_138l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_311_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_138l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_311 :
    hubcapFit theRedpart rf9 p9_138l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_311_1, c9_311_2, c9_311_3, c9_311_4, c9_311_5, c9_311_6, c9_311_7, c9_311_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_326r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_326r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_326r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_326r) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_326r) (hubSubn 9 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_327_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_326r) (hubSubn 9 4 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_327 :
    hubcapFit theRedpart rf9 p9_326r
    (Hubcap.two 2 3 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_327_1, c9_327_2, c9_327_3, c9_327_4, c9_327_5, c9_327_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_326l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_326l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_326l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_328_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_326l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_328 :
    hubcapFit theRedpart rf9 p9_326l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_328_1, c9_328_2, c9_328_3, c9_328_4, c9_328_5, c9_328_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_325l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_325l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_325l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_330_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_325l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_330 :
    hubcapFit theRedpart rf9 p9_325l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_330_1, c9_330_2, c9_330_3, c9_330_4, c9_330_5, c9_330_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_324l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_324l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_331_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_324l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_331 :
    hubcapFit theRedpart rf9 p9_324l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_331_1, c9_331_2, c9_331_3, c9_331_4, c9_331_5, c9_331_6, c9_331_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_323l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_323l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_333_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_323l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_333 :
    hubcapFit theRedpart rf9 p9_323l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_333_1, c9_333_2, c9_333_3, c9_333_4, c9_333_5, c9_333_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_322l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_322l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_322l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_322l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_322l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_334_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_322l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_334 :
    hubcapFit theRedpart rf9 p9_322l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_334_1, c9_334_2, c9_334_3, c9_334_4, c9_334_5, c9_334_6, c9_334_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_321l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_321l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_321l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_336_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_321l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_336 :
    hubcapFit theRedpart rf9 p9_321l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_336_1, c9_336_2, c9_336_3, c9_336_4, c9_336_5, c9_336_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_320l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_320l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_337_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_320l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_337 :
    hubcapFit theRedpart rf9 p9_320l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_337_1, c9_337_2, c9_337_3, c9_337_4, c9_337_5, c9_337_6, c9_337_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_351r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_351r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_352_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_351r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_352 :
    hubcapFit theRedpart rf9 p9_351r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_352_1, c9_352_2, c9_352_3, c9_352_4, c9_352_5, c9_352_6, c9_352_7, c9_352_8]

end FourColor

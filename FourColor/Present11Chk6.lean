import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_310_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_310 :
    hubcapFit theRedpart rf11 p11_261l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_310_1, c11_310_2, c11_310_3, c11_310_4, c11_310_5, c11_310_6, c11_310_7, c11_310_8, c11_310_9, c11_310_10, c11_310_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_1l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_1l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_1l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_317_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_1l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_317 :
    hubcapFit theRedpart rf11 p11_1l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_317_1, c11_317_2, c11_317_3, c11_317_4, c11_317_5, c11_317_6, c11_317_7, c11_317_8, c11_317_9, c11_317_10, c11_317_11]

end FourColor

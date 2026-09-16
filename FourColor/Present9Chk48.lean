import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 48 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2270l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2270l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2270l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2270l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2270l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2276_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2270l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2276 :
    hubcapFit theRedpart rf9 p9_2270l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2276_1, c9_2276_2, c9_2276_3, c9_2276_4, c9_2276_5, c9_2276_6, c9_2276_7, c9_2276_8, c9_2276_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2269l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2269l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2278_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2269l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2278 :
    hubcapFit theRedpart rf9 p9_2269l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2278_1, c9_2278_2, c9_2278_3, c9_2278_4, c9_2278_5, c9_2278_6, c9_2278_7, c9_2278_8, c9_2278_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2266l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2266l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2266l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2280_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2280 :
    hubcapFit theRedpart rf9 p9_2266l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2280_1, c9_2280_2, c9_2280_3, c9_2280_4, c9_2280_5, c9_2280_6, c9_2280_7, c9_2280_8, c9_2280_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2264l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2282_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2264l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2282 :
    hubcapFit theRedpart rf9 p9_2264l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2282_1, c9_2282_2, c9_2282_3, c9_2282_4, c9_2282_5, c9_2282_6, c9_2282_7, c9_2282_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2261l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2284_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2261l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2284 :
    hubcapFit theRedpart rf9 p9_2261l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2284_1, c9_2284_2, c9_2284_3, c9_2284_4, c9_2284_5, c9_2284_6, c9_2284_7, c9_2284_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2291l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2292_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2291l) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2292 :
    hubcapFit theRedpart rf9 p9_2291l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2292_1, c9_2292_2, c9_2292_3, c9_2292_4, c9_2292_5, c9_2292_6, c9_2292_7, c9_2292_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2291r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2291r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2291r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2291r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2291r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2291r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2291r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2294_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2291r) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2294 :
    hubcapFit theRedpart rf9 p9_2291r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2294_1, c9_2294_2, c9_2294_3, c9_2294_4, c9_2294_5, c9_2294_6, c9_2294_7, c9_2294_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2297l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2297l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2297l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2298_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2297l) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2298 :
    hubcapFit theRedpart rf9 p9_2297l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2298_1, c9_2298_2, c9_2298_3, c9_2298_4, c9_2298_5, c9_2298_6, c9_2298_7, c9_2298_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2297r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2297r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2297r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2297r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2300_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2297r) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2300 :
    hubcapFit theRedpart rf9 p9_2297r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2300_1, c9_2300_2, c9_2300_3, c9_2300_4, c9_2300_5, c9_2300_6, c9_2300_7, c9_2300_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2289r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2289r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2289r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2289r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2289r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2289r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2289r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2304_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2289r) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2304 :
    hubcapFit theRedpart rf9 p9_2289r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2304_1, c9_2304_2, c9_2304_3, c9_2304_4, c9_2304_5, c9_2304_6, c9_2304_7, c9_2304_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2288r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2288r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2288r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2288r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2288r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2288r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2288r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2307_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2288r) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2307 :
    hubcapFit theRedpart rf9 p9_2288r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2307_1, c9_2307_2, c9_2307_3, c9_2307_4, c9_2307_5, c9_2307_6, c9_2307_7, c9_2307_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2336r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2336r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2337_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2336r) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2337 :
    hubcapFit theRedpart rf9 p9_2336r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2337_1, c9_2337_2, c9_2337_3, c9_2337_4, c9_2337_5, c9_2337_6, c9_2337_7, c9_2337_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2338_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2336l) (hubSubn 9 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2338 :
    hubcapFit theRedpart rf9 p9_2336l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2338_1, c9_2338_2, c9_2338_3, c9_2338_4, c9_2338_5, c9_2338_6, c9_2338_7, c9_2338_8]

end FourColor

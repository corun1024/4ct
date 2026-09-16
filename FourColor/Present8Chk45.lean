import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 45 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2284l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2284l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2284l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2292_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2284l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2292 :
    hubcapFit theRedpart rf8 p8_2284l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2292_1, c8_2292_2, c8_2292_3, c8_2292_4, c8_2292_5, c8_2292_6, c8_2292_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2283l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2294_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2283l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2294 :
    hubcapFit theRedpart rf8 p8_2283l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2294_1, c8_2294_2, c8_2294_3, c8_2294_4, c8_2294_5, c8_2294_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2282l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2295_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2282l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2295 :
    hubcapFit theRedpart rf8 p8_2282l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2295_1, c8_2295_2, c8_2295_3, c8_2295_4, c8_2295_5, c8_2295_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2281l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2281l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2297_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2297 :
    hubcapFit theRedpart rf8 p8_2281l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2297_1, c8_2297_2, c8_2297_3, c8_2297_4, c8_2297_5, c8_2297_6, c8_2297_7, c8_2297_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2280l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2280l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2280l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2299_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2299 :
    hubcapFit theRedpart rf8 p8_2280l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2299_1, c8_2299_2, c8_2299_3, c8_2299_4, c8_2299_5, c8_2299_6, c8_2299_7, c8_2299_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2301_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2301 :
    hubcapFit theRedpart rf8 p8_2279l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2301_1, c8_2301_2, c8_2301_3, c8_2301_4, c8_2301_5, c8_2301_6, c8_2301_7, c8_2301_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2278l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2278l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2278l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2303_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2278l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2303 :
    hubcapFit theRedpart rf8 p8_2278l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2303_1, c8_2303_2, c8_2303_3, c8_2303_4, c8_2303_5, c8_2303_6, c8_2303_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2277l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2277l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2277l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2277l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2277l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2277l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2305_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2277l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2305 :
    hubcapFit theRedpart rf8 p8_2277l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2305_1, c8_2305_2, c8_2305_3, c8_2305_4, c8_2305_5, c8_2305_6, c8_2305_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2313_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2312r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2313_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2312r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2313_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2312r) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2313_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2312r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2313_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2312r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2313 :
    hubcapFit theRedpart rf8 p8_2312r
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2313_1, c8_2313_2, c8_2313_3, c8_2313_4, c8_2313_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2316r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2316r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2316r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2316r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2316r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2317_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2316r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2317 :
    hubcapFit theRedpart rf8 p8_2316r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2317_1, c8_2317_2, c8_2317_3, c8_2317_4, c8_2317_5, c8_2317_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2316l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2316l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2316l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2316l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2318_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2316l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2318 :
    hubcapFit theRedpart rf8 p8_2316l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2318_1, c8_2318_2, c8_2318_3, c8_2318_4, c8_2318_5, c8_2318_6, c8_2318_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2315l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2315l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2315l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2315l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2320_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2315l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2320 :
    hubcapFit theRedpart rf8 p8_2315l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2320_1, c8_2320_2, c8_2320_3, c8_2320_4, c8_2320_5, c8_2320_6, c8_2320_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2309l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2309l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2309l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2309l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2309l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2322_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2309l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2322 :
    hubcapFit theRedpart rf8 p8_2309l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2322_1, c8_2322_2, c8_2322_3, c8_2322_4, c8_2322_5, c8_2322_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2308l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2308l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2308l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2308l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2324_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2308l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2324 :
    hubcapFit theRedpart rf8 p8_2308l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2324_1, c8_2324_2, c8_2324_3, c8_2324_4, c8_2324_5, c8_2324_6, c8_2324_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2307l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2307l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2326_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2307l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2326 :
    hubcapFit theRedpart rf8 p8_2307l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2326_1, c8_2326_2, c8_2326_3, c8_2326_4, c8_2326_5, c8_2326_6, c8_2326_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2328_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2328_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2328_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2227l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2328_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2227l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2328_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2227l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2328 :
    hubcapFit theRedpart rf8 p8_2227l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2328_1, c8_2328_2, c8_2328_3, c8_2328_4, c8_2328_5]

end FourColor

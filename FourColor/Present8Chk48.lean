import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 48 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2429l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2429l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2435_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2435 :
    hubcapFit theRedpart rf8 p8_2429l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2435_1, c8_2435_2, c8_2435_3, c8_2435_4, c8_2435_5, c8_2435_6, c8_2435_7, c8_2435_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2427l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2427l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2427l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2427l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2437_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2427l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2437 :
    hubcapFit theRedpart rf8 p8_2427l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2437_1, c8_2437_2, c8_2437_3, c8_2437_4, c8_2437_5, c8_2437_6, c8_2437_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2426l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2426l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2439_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2426l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2439 :
    hubcapFit theRedpart rf8 p8_2426l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2439_1, c8_2439_2, c8_2439_3, c8_2439_4, c8_2439_5, c8_2439_6, c8_2439_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2406l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2406l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2406l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2406l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2406l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2406l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2441_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2406l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2441 :
    hubcapFit theRedpart rf8 p8_2406l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2441_1, c8_2441_2, c8_2441_3, c8_2441_4, c8_2441_5, c8_2441_6, c8_2441_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2405l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2405l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2405l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2443_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2405l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2443 :
    hubcapFit theRedpart rf8 p8_2405l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2443_1, c8_2443_2, c8_2443_3, c8_2443_4, c8_2443_5, c8_2443_6, c8_2443_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2452r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2452r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2452r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2452r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2452r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2452r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2452r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2453_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2452r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2453 :
    hubcapFit theRedpart rf8 p8_2452r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2453_1, c8_2453_2, c8_2453_3, c8_2453_4, c8_2453_5, c8_2453_6, c8_2453_7, c8_2453_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2454_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2454 :
    hubcapFit theRedpart rf8 p8_2452l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2454_1, c8_2454_2, c8_2454_3, c8_2454_4, c8_2454_5, c8_2454_6, c8_2454_7, c8_2454_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2450l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2450l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2450l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2450l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2450l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2456_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2450l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2456 :
    hubcapFit theRedpart rf8 p8_2450l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2456_1, c8_2456_2, c8_2456_3, c8_2456_4, c8_2456_5, c8_2456_6, c8_2456_7, c8_2456_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2449l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2449l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2449l) (hubSubn 8 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2458_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2449l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2458 :
    hubcapFit theRedpart rf8 p8_2449l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2458_1, c8_2458_2, c8_2458_3, c8_2458_4, c8_2458_5, c8_2458_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2448l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2459_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2459 :
    hubcapFit theRedpart rf8 p8_2448l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2459_1, c8_2459_2, c8_2459_3, c8_2459_4, c8_2459_5, c8_2459_6, c8_2459_7, c8_2459_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2447l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2447l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2447l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2447l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2461_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2447l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2461 :
    hubcapFit theRedpart rf8 p8_2447l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2461_1, c8_2461_2, c8_2461_3, c8_2461_4, c8_2461_5, c8_2461_6, c8_2461_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2463_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2463 :
    hubcapFit theRedpart rf8 p8_2446l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2463_1, c8_2463_2, c8_2463_3, c8_2463_4, c8_2463_5, c8_2463_6, c8_2463_7, c8_2463_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2445l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2465_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2445l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2465 :
    hubcapFit theRedpart rf8 p8_2445l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2465_1, c8_2465_2, c8_2465_3, c8_2465_4, c8_2465_5, c8_2465_6, c8_2465_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2472r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2472r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2472r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2472r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2472r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2473_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2472r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2473 :
    hubcapFit theRedpart rf8 p8_2472r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2473_1, c8_2473_2, c8_2473_3, c8_2473_4, c8_2473_5, c8_2473_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2472l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2474_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2472l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2474 :
    hubcapFit theRedpart rf8 p8_2472l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2474_1, c8_2474_2, c8_2474_3, c8_2474_4, c8_2474_5, c8_2474_6]

end FourColor

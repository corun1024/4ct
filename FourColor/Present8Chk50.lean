import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 50 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2526l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2528_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2526l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2528 :
    hubcapFit theRedpart rf8 p8_2526l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2528_1, c8_2528_2, c8_2528_3, c8_2528_4, c8_2528_5, c8_2528_6, c8_2528_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2524l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2524l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2530_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2524l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2530 :
    hubcapFit theRedpart rf8 p8_2524l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2530_1, c8_2530_2, c8_2530_3, c8_2530_4, c8_2530_5, c8_2530_6, c8_2530_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2514l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2514l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2514l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2532_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2514l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2532 :
    hubcapFit theRedpart rf8 p8_2514l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2532_1, c8_2532_2, c8_2532_3, c8_2532_4, c8_2532_5, c8_2532_6, c8_2532_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2513l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2513l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2513l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2513l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2513l) (hubSubn 8 4 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2534_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2513l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2534 :
    hubcapFit theRedpart rf8 p8_2513l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2534_1, c8_2534_2, c8_2534_3, c8_2534_4, c8_2534_5, c8_2534_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2512l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2512l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2512l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2512l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2512l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2512l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2535_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2512l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2535 :
    hubcapFit theRedpart rf8 p8_2512l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2535_1, c8_2535_2, c8_2535_3, c8_2535_4, c8_2535_5, c8_2535_6, c8_2535_7, c8_2535_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2544r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2544r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2544r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2544r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2544r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2544r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2545_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2544r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2545 :
    hubcapFit theRedpart rf8 p8_2544r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2545_1, c8_2545_2, c8_2545_3, c8_2545_4, c8_2545_5, c8_2545_6, c8_2545_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2544l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2544l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2544l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2544l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2544l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2546_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2544l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2546 :
    hubcapFit theRedpart rf8 p8_2544l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2546_1, c8_2546_2, c8_2546_3, c8_2546_4, c8_2546_5, c8_2546_6, c8_2546_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2542l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2548_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2542l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2548 :
    hubcapFit theRedpart rf8 p8_2542l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2548_1, c8_2548_2, c8_2548_3, c8_2548_4, c8_2548_5, c8_2548_6, c8_2548_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2541l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2541l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2541l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2541l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2541l) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2550_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2541l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2550 :
    hubcapFit theRedpart rf8 p8_2541l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2550_1, c8_2550_2, c8_2550_3, c8_2550_4, c8_2550_5, c8_2550_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2551_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2540l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2551_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2540l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2551_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2540l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2551_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2540l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2551_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2540l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2551 :
    hubcapFit theRedpart rf8 p8_2540l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2551_1, c8_2551_2, c8_2551_3, c8_2551_4, c8_2551_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2539l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2539l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2539l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2539l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2539l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2539l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2553_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2539l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2553 :
    hubcapFit theRedpart rf8 p8_2539l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2553_1, c8_2553_2, c8_2553_3, c8_2553_4, c8_2553_5, c8_2553_6, c8_2553_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2538l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2538l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2538l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2538l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2538l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2538l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2555_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2538l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2555 :
    hubcapFit theRedpart rf8 p8_2538l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2555_1, c8_2555_2, c8_2555_3, c8_2555_4, c8_2555_5, c8_2555_6, c8_2555_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2537l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2537l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2537l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2537l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2537l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2537l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2537l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2557_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2537l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2557 :
    hubcapFit theRedpart rf8 p8_2537l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2557_1, c8_2557_2, c8_2557_3, c8_2557_4, c8_2557_5, c8_2557_6, c8_2557_7, c8_2557_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2566r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2566r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2566r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2566r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2566r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2567_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2566r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2567 :
    hubcapFit theRedpart rf8 p8_2566r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2567_1, c8_2567_2, c8_2567_3, c8_2567_4, c8_2567_5, c8_2567_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2566l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2566l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2566l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2566l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2568_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2566l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2568 :
    hubcapFit theRedpart rf8 p8_2566l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2568_1, c8_2568_2, c8_2568_3, c8_2568_4, c8_2568_5, c8_2568_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2570l) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2571_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2570l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2571 :
    hubcapFit theRedpart rf8 p8_2570l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2571_1, c8_2571_2, c8_2571_3, c8_2571_4, c8_2571_5, c8_2571_6]

end FourColor

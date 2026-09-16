import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 49 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2471l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2471l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2471l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2471l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2471l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2476_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2471l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2476 :
    hubcapFit theRedpart rf8 p8_2471l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2476_1, c8_2476_2, c8_2476_3, c8_2476_4, c8_2476_5, c8_2476_6, c8_2476_7, c8_2476_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2470l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2470l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2470l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2470l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2470l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2470l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2478_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2470l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2478 :
    hubcapFit theRedpart rf8 p8_2470l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2478_1, c8_2478_2, c8_2478_3, c8_2478_4, c8_2478_5, c8_2478_6, c8_2478_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2469l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2469l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2469l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2480_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2469l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2480 :
    hubcapFit theRedpart rf8 p8_2469l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2480_1, c8_2480_2, c8_2480_3, c8_2480_4, c8_2480_5, c8_2480_6, c8_2480_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2468l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2468l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2468l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2482_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2468l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2482 :
    hubcapFit theRedpart rf8 p8_2468l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2482_1, c8_2482_2, c8_2482_3, c8_2482_4, c8_2482_5, c8_2482_6, c8_2482_7, c8_2482_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2340l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2340l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2340l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2484_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2340l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2484 :
    hubcapFit theRedpart rf8 p8_2340l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2484_1, c8_2484_2, c8_2484_3, c8_2484_4, c8_2484_5, c8_2484_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2498r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2498r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2498r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2498r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2499_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2498r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2499 :
    hubcapFit theRedpart rf8 p8_2498r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2499_1, c8_2499_2, c8_2499_3, c8_2499_4, c8_2499_5, c8_2499_6, c8_2499_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2498l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2498l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2498l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2500_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2498l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2500 :
    hubcapFit theRedpart rf8 p8_2498l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2500_1, c8_2500_2, c8_2500_3, c8_2500_4, c8_2500_5, c8_2500_6, c8_2500_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2502_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2502_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2502_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2497l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2502_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2497l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2502_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2497l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2502 :
    hubcapFit theRedpart rf8 p8_2497l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2502_1, c8_2502_2, c8_2502_3, c8_2502_4, c8_2502_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2504r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2504r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2504r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2504r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2504r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2505_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2504r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2505 :
    hubcapFit theRedpart rf8 p8_2504r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2505_1, c8_2505_2, c8_2505_3, c8_2505_4, c8_2505_5, c8_2505_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2506_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2504l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2506 :
    hubcapFit theRedpart rf8 p8_2504l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2506_1, c8_2506_2, c8_2506_3, c8_2506_4, c8_2506_5, c8_2506_6, c8_2506_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2494l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2494l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2494l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2494l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2494l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2508_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2494l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2508 :
    hubcapFit theRedpart rf8 p8_2494l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2508_1, c8_2508_2, c8_2508_3, c8_2508_4, c8_2508_5, c8_2508_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2493l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2493l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2493l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2493l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2493l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2493l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2510_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2493l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2510 :
    hubcapFit theRedpart rf8 p8_2493l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2510_1, c8_2510_2, c8_2510_3, c8_2510_4, c8_2510_5, c8_2510_6, c8_2510_7, c8_2510_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2518r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2518r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2518r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2518r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2518r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2518r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2519_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2518r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2519 :
    hubcapFit theRedpart rf8 p8_2518r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2519_1, c8_2519_2, c8_2519_3, c8_2519_4, c8_2519_5, c8_2519_6, c8_2519_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2518l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2518l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2518l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2518l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2518l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2518l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2520_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2518l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2520 :
    hubcapFit theRedpart rf8 p8_2518l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2520_1, c8_2520_2, c8_2520_3, c8_2520_4, c8_2520_5, c8_2520_6, c8_2520_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2516l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2516l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2516l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2516l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2522_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2516l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2522 :
    hubcapFit theRedpart rf8 p8_2516l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2522_1, c8_2522_2, c8_2522_3, c8_2522_4, c8_2522_5, c8_2522_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2526r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2526r) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2527_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2526r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2527 :
    hubcapFit theRedpart rf8 p8_2526r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2527_1, c8_2527_2, c8_2527_3, c8_2527_4, c8_2527_5, c8_2527_6]

end FourColor

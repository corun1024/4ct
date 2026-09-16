import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 51 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2414l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2419_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2414l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2419 :
    hubcapFit theRedpart rf9 p9_2414l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2419_1, c9_2419_2, c9_2419_3, c9_2419_4, c9_2419_5, c9_2419_6, c9_2419_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2413l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2413l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2421_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2413l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2421 :
    hubcapFit theRedpart rf9 p9_2413l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2421_1, c9_2421_2, c9_2421_3, c9_2421_4, c9_2421_5, c9_2421_6, c9_2421_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2423_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2411l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2423 :
    hubcapFit theRedpart rf9 p9_2411l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2423_1, c9_2423_2, c9_2423_3, c9_2423_4, c9_2423_5, c9_2423_6, c9_2423_7, c9_2423_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2410l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2410l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2410l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2410l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2410l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2410l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2425_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2410l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2425 :
    hubcapFit theRedpart rf9 p9_2410l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2425_1, c9_2425_2, c9_2425_3, c9_2425_4, c9_2425_5, c9_2425_6, c9_2425_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2318l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2318l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2428_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2318l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2428 :
    hubcapFit theRedpart rf9 p9_2318l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2428_1, c9_2428_2, c9_2428_3, c9_2428_4, c9_2428_5, c9_2428_6, c9_2428_7, c9_2428_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2317l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2430_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2317l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2430 :
    hubcapFit theRedpart rf9 p9_2317l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2430_1, c9_2430_2, c9_2430_3, c9_2430_4, c9_2430_5, c9_2430_6, c9_2430_7, c9_2430_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2316l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2316l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2432_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2316l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2432 :
    hubcapFit theRedpart rf9 p9_2316l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2432_1, c9_2432_2, c9_2432_3, c9_2432_4, c9_2432_5, c9_2432_6, c9_2432_7, c9_2432_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2434_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2315l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2434 :
    hubcapFit theRedpart rf9 p9_2315l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2434_1, c9_2434_2, c9_2434_3, c9_2434_4, c9_2434_5, c9_2434_6, c9_2434_7, c9_2434_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2314l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2314l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2436_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2314l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2436 :
    hubcapFit theRedpart rf9 p9_2314l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2436_1, c9_2436_2, c9_2436_3, c9_2436_4, c9_2436_5, c9_2436_6, c9_2436_7, c9_2436_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2445r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2445r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2445r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2445r) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2445r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2446_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2445r) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2446 :
    hubcapFit theRedpart rf9 p9_2445r
    (Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2446_1, c9_2446_2, c9_2446_3, c9_2446_4, c9_2446_5, c9_2446_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2452r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2452r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2452r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2452r) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2452r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2453_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2452r) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2453 :
    hubcapFit theRedpart rf9 p9_2452r
    (Hubcap.one 1 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2453_1, c9_2453_2, c9_2453_3, c9_2453_4, c9_2453_5, c9_2453_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2452l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2454_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2452l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2454 :
    hubcapFit theRedpart rf9 p9_2452l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2454_1, c9_2454_2, c9_2454_3, c9_2454_4, c9_2454_5, c9_2454_6, c9_2454_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2451l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2451l) (hubSubn 9 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2456_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2451l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2456 :
    hubcapFit theRedpart rf9 p9_2451l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2456_1, c9_2456_2, c9_2456_3, c9_2456_4, c9_2456_5, c9_2456_6, c9_2456_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2450l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2458_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2450l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2458 :
    hubcapFit theRedpart rf9 p9_2450l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2458_1, c9_2458_2, c9_2458_3, c9_2458_4, c9_2458_5, c9_2458_6, c9_2458_7, c9_2458_8]

end FourColor

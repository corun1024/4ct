import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 53 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2669l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2669l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2680_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2680 :
    hubcapFit theRedpart rf8 p8_2669l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2680_1, c8_2680_2, c8_2680_3, c8_2680_4, c8_2680_5, c8_2680_6, c8_2680_7, c8_2680_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2668l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2668l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2682_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2668l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2682 :
    hubcapFit theRedpart rf8 p8_2668l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2682_1, c8_2682_2, c8_2682_3, c8_2682_4, c8_2682_5, c8_2682_6, c8_2682_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2685r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2685r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2685r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2685r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2685r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2685r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2686_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2685r) (hubSubn 8 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2686 :
    hubcapFit theRedpart rf8 p8_2685r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2686_1, c8_2686_2, c8_2686_3, c8_2686_4, c8_2686_5, c8_2686_6, c8_2686_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2685l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2685l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2687_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2685l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2687 :
    hubcapFit theRedpart rf8 p8_2685l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2687_1, c8_2687_2, c8_2687_3, c8_2687_4, c8_2687_5, c8_2687_6, c8_2687_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2684l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2684l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2684l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2684l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2684l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2689_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2684l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2689 :
    hubcapFit theRedpart rf8 p8_2684l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2689_1, c8_2689_2, c8_2689_3, c8_2689_4, c8_2689_5, c8_2689_6, c8_2689_7, c8_2689_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2663l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2692_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2663l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2692 :
    hubcapFit theRedpart rf8 p8_2663l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2692_1, c8_2692_2, c8_2692_3, c8_2692_4, c8_2692_5, c8_2692_6, c8_2692_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2703r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2703r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2703r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2703r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2703r) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2704_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2703r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2704 :
    hubcapFit theRedpart rf8 p8_2703r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2704_1, c8_2704_2, c8_2704_3, c8_2704_4, c8_2704_5, c8_2704_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2703l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2703l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2703l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2703l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2703l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2705_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2703l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2705 :
    hubcapFit theRedpart rf8 p8_2703l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2705_1, c8_2705_2, c8_2705_3, c8_2705_4, c8_2705_5, c8_2705_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2702l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2702l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2702l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2702l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2707_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2707 :
    hubcapFit theRedpart rf8 p8_2702l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2707_1, c8_2707_2, c8_2707_3, c8_2707_4, c8_2707_5, c8_2707_6, c8_2707_7, c8_2707_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2701l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2701l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2701l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2709_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2709 :
    hubcapFit theRedpart rf8 p8_2701l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2709_1, c8_2709_2, c8_2709_3, c8_2709_4, c8_2709_5, c8_2709_6, c8_2709_7, c8_2709_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2700l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2700l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2700l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2700l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2711_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2700l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2711 :
    hubcapFit theRedpart rf8 p8_2700l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2711_1, c8_2711_2, c8_2711_3, c8_2711_4, c8_2711_5, c8_2711_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2716r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2716r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2716r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2716r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2716r) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2717_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2716r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2717 :
    hubcapFit theRedpart rf8 p8_2716r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2717_1, c8_2717_2, c8_2717_3, c8_2717_4, c8_2717_5, c8_2717_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2716l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2718_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2718 :
    hubcapFit theRedpart rf8 p8_2716l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2718_1, c8_2718_2, c8_2718_3, c8_2718_4, c8_2718_5, c8_2718_6, c8_2718_7, c8_2718_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2714l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2714l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2714l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2714l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2720_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2714l) (hubSubn 8 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2720 :
    hubcapFit theRedpart rf8 p8_2714l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 5 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2720_1, c8_2720_2, c8_2720_3, c8_2720_4, c8_2720_5, c8_2720_6, c8_2720_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2713l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2713l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2722_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2713l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2722 :
    hubcapFit theRedpart rf8 p8_2713l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2722_1, c8_2722_2, c8_2722_3, c8_2722_4, c8_2722_5, c8_2722_6]

end FourColor

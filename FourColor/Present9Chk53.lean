import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 53 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2487l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2500_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2487l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2500 :
    hubcapFit theRedpart rf9 p9_2487l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2500_1, c9_2500_2, c9_2500_3, c9_2500_4, c9_2500_5, c9_2500_6, c9_2500_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2486l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2486l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2502_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2486l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2502 :
    hubcapFit theRedpart rf9 p9_2486l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2502_1, c9_2502_2, c9_2502_3, c9_2502_4, c9_2502_5, c9_2502_6, c9_2502_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2485l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2485l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2504_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2485l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2504 :
    hubcapFit theRedpart rf9 p9_2485l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2504_1, c9_2504_2, c9_2504_3, c9_2504_4, c9_2504_5, c9_2504_6, c9_2504_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2484l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2506_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2484l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2506 :
    hubcapFit theRedpart rf9 p9_2484l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2506_1, c9_2506_2, c9_2506_3, c9_2506_4, c9_2506_5, c9_2506_6, c9_2506_7, c9_2506_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2469l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2469l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2508_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2469l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2508 :
    hubcapFit theRedpart rf9 p9_2469l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2508_1, c9_2508_2, c9_2508_3, c9_2508_4, c9_2508_5, c9_2508_6, c9_2508_7, c9_2508_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2510l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2510l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2510l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2511_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2510l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2511 :
    hubcapFit theRedpart rf9 p9_2510l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2511_1, c9_2511_2, c9_2511_3, c9_2511_4, c9_2511_5, c9_2511_6, c9_2511_7, c9_2511_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2513l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2513l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2513l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2514_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2513l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2514 :
    hubcapFit theRedpart rf9 p9_2513l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2514_1, c9_2514_2, c9_2514_3, c9_2514_4, c9_2514_5, c9_2514_6, c9_2514_7, c9_2514_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2516l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2516l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2516l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2517_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2516l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2517 :
    hubcapFit theRedpart rf9 p9_2516l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2517_1, c9_2517_2, c9_2517_3, c9_2517_4, c9_2517_5, c9_2517_6, c9_2517_7, c9_2517_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2516r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2516r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2516r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2516r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2516r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2516r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2516r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2519_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2516r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2519 :
    hubcapFit theRedpart rf9 p9_2516r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2519_1, c9_2519_2, c9_2519_3, c9_2519_4, c9_2519_5, c9_2519_6, c9_2519_7, c9_2519_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2525l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2525l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2525l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2526_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2525l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2526 :
    hubcapFit theRedpart rf9 p9_2525l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2526_1, c9_2526_2, c9_2526_3, c9_2526_4, c9_2526_5, c9_2526_6, c9_2526_7, c9_2526_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2529_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2528l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2529 :
    hubcapFit theRedpart rf9 p9_2528l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2529_1, c9_2529_2, c9_2529_3, c9_2529_4, c9_2529_5, c9_2529_6, c9_2529_7, c9_2529_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2531l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2531l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2531l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2531l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2531l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2532_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2531l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2532 :
    hubcapFit theRedpart rf9 p9_2531l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2532_1, c9_2532_2, c9_2532_3, c9_2532_4, c9_2532_5, c9_2532_6, c9_2532_7, c9_2532_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2531r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2531r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2531r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2531r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2531r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2531r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2531r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2534_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2531r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2534 :
    hubcapFit theRedpart rf9 p9_2531r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2534_1, c9_2534_2, c9_2534_3, c9_2534_4, c9_2534_5, c9_2534_6, c9_2534_7, c9_2534_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2575r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2575r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2575r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2575r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2575r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2575r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2576_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2575r) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2576 :
    hubcapFit theRedpart rf9 p9_2575r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2576_1, c9_2576_2, c9_2576_3, c9_2576_4, c9_2576_5, c9_2576_6, c9_2576_7]

end FourColor

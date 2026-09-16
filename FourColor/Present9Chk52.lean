import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 52 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2460_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2449l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2460 :
    hubcapFit theRedpart rf9 p9_2449l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2460_1, c9_2460_2, c9_2460_3, c9_2460_4, c9_2460_5, c9_2460_6, c9_2460_7, c9_2460_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2462_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2448l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2462 :
    hubcapFit theRedpart rf9 p9_2448l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2462_1, c9_2462_2, c9_2462_3, c9_2462_4, c9_2462_5, c9_2462_6, c9_2462_7, c9_2462_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2464_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2443l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2464 :
    hubcapFit theRedpart rf9 p9_2443l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2464_1, c9_2464_2, c9_2464_3, c9_2464_4, c9_2464_5, c9_2464_6, c9_2464_7, c9_2464_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2442l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2466_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2442l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2466 :
    hubcapFit theRedpart rf9 p9_2442l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2466_1, c9_2466_2, c9_2466_3, c9_2466_4, c9_2466_5, c9_2466_6, c9_2466_7, c9_2466_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2475r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2475r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2475r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2475r) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2475r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2476_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2475r) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2476 :
    hubcapFit theRedpart rf9 p9_2475r
    (Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2476_1, c9_2476_2, c9_2476_3, c9_2476_4, c9_2476_5, c9_2476_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2475l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2477_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2475l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2477 :
    hubcapFit theRedpart rf9 p9_2475l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2477_1, c9_2477_2, c9_2477_3, c9_2477_4, c9_2477_5, c9_2477_6, c9_2477_7, c9_2477_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2474l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2474l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2479_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2474l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2479 :
    hubcapFit theRedpart rf9 p9_2474l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2479_1, c9_2479_2, c9_2479_3, c9_2479_4, c9_2479_5, c9_2479_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2473l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2473l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2480_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2473l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2480 :
    hubcapFit theRedpart rf9 p9_2473l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2480_1, c9_2480_2, c9_2480_3, c9_2480_4, c9_2480_5, c9_2480_6, c9_2480_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2472l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2472l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2482_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2472l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2482 :
    hubcapFit theRedpart rf9 p9_2472l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2482_1, c9_2482_2, c9_2482_3, c9_2482_4, c9_2482_5, c9_2482_6, c9_2482_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2491r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2491r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2492_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2491r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2492 :
    hubcapFit theRedpart rf9 p9_2491r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2492_1, c9_2492_2, c9_2492_3, c9_2492_4, c9_2492_5, c9_2492_6, c9_2492_7, c9_2492_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2491l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2493_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2493 :
    hubcapFit theRedpart rf9 p9_2491l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2493_1, c9_2493_2, c9_2493_3, c9_2493_4, c9_2493_5, c9_2493_6, c9_2493_7, c9_2493_8, c9_2493_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2490l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2495_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2490l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2495 :
    hubcapFit theRedpart rf9 p9_2490l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2495_1, c9_2495_2, c9_2495_3, c9_2495_4, c9_2495_5, c9_2495_6, c9_2495_7, c9_2495_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2489l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2489l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2497_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2489l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2497 :
    hubcapFit theRedpart rf9 p9_2489l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2497_1, c9_2497_2, c9_2497_3, c9_2497_4, c9_2497_5, c9_2497_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2498_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2488l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2498 :
    hubcapFit theRedpart rf9 p9_2488l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2498_1, c9_2498_2, c9_2498_3, c9_2498_4, c9_2498_5, c9_2498_6, c9_2498_7, c9_2498_8]

end FourColor

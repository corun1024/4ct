import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 44 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2424l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2424l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2431_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2424l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2431 :
    hubcapFit theRedpart rf7 p7_2424l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2431_1, c7_2431_2, c7_2431_3, c7_2431_4, c7_2431_5, c7_2431_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2423l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2423l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2423l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2423l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2433_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2423l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2433 :
    hubcapFit theRedpart rf7 p7_2423l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2433_1, c7_2433_2, c7_2433_3, c7_2433_4, c7_2433_5, c7_2433_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2434_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2434_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2422l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2434_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2422l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2434_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2422l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2434_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2422l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2434 :
    hubcapFit theRedpart rf7 p7_2422l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2434_1, c7_2434_2, c7_2434_3, c7_2434_4, c7_2434_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2421l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2421l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2421l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2421l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2421l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2436_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2421l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2436 :
    hubcapFit theRedpart rf7 p7_2421l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2436_1, c7_2436_2, c7_2436_3, c7_2436_4, c7_2436_5, c7_2436_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2442_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2441r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2442_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2441r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2442_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2441r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2442_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2441r) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2442_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2441r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2442 :
    hubcapFit theRedpart rf7 p7_2441r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2442_1, c7_2442_2, c7_2442_3, c7_2442_4, c7_2442_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2441l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2441l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2441l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2443_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2443 :
    hubcapFit theRedpart rf7 p7_2441l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2443_1, c7_2443_2, c7_2443_3, c7_2443_4, c7_2443_5, c7_2443_6, c7_2443_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2440l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2440l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2440l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2440l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2440l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2445_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2440l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2445 :
    hubcapFit theRedpart rf7 p7_2440l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2445_1, c7_2445_2, c7_2445_3, c7_2445_4, c7_2445_5, c7_2445_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2448r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2448r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2448r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2448r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2448r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2449_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2448r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2449 :
    hubcapFit theRedpart rf7 p7_2448r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2449_1, c7_2449_2, c7_2449_3, c7_2449_4, c7_2449_5, c7_2449_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2448l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2450_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2448l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2450 :
    hubcapFit theRedpart rf7 p7_2448l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2450_1, c7_2450_2, c7_2450_3, c7_2450_4, c7_2450_5, c7_2450_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2447l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2447l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2447l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2452_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2447l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2452 :
    hubcapFit theRedpart rf7 p7_2447l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2452_1, c7_2452_2, c7_2452_3, c7_2452_4, c7_2452_5, c7_2452_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2458r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2458r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2458r) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2458r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2458r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2459_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2458r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2459 :
    hubcapFit theRedpart rf7 p7_2458r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2459_1, c7_2459_2, c7_2459_3, c7_2459_4, c7_2459_5, c7_2459_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2460_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2458l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2460_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2458l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2460_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2458l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2460_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2458l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2460_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2458l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2460 :
    hubcapFit theRedpart rf7 p7_2458l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2460_1, c7_2460_2, c7_2460_3, c7_2460_4, c7_2460_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2462_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2457l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2462_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2457l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2462_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2457l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2462_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2457l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2462_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2457l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2462 :
    hubcapFit theRedpart rf7 p7_2457l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2462_1, c7_2462_2, c7_2462_3, c7_2462_4, c7_2462_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2466r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2466r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2466r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2466r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2466r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2467_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2466r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2467 :
    hubcapFit theRedpart rf7 p7_2466r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2467_1, c7_2467_2, c7_2467_3, c7_2467_4, c7_2467_5, c7_2467_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2465l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2468_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2465l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2468 :
    hubcapFit theRedpart rf7 p7_2465l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2468_1, c7_2468_2, c7_2468_3, c7_2468_4, c7_2468_5, c7_2468_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2464l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2464l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2464l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2464l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2464l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2470_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2464l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2470 :
    hubcapFit theRedpart rf7 p7_2464l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2470_1, c7_2470_2, c7_2470_3, c7_2470_4, c7_2470_5, c7_2470_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2476_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2475r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2476_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2475r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2476_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2475r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2476_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2475r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2476_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2475r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2476 :
    hubcapFit theRedpart rf7 p7_2475r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2476_1, c7_2476_2, c7_2476_3, c7_2476_4, c7_2476_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2477_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2477_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2474l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2477_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2477_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2474l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2477_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2474l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2477 :
    hubcapFit theRedpart rf7 p7_2474l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2477_1, c7_2477_2, c7_2477_3, c7_2477_4, c7_2477_5]

end FourColor

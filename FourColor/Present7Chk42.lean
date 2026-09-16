import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 42 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2327r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2327r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2327r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2327r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2327r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2327r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2328_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2327r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2328 :
    hubcapFit theRedpart rf7 p7_2327r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2328_1, c7_2328_2, c7_2328_3, c7_2328_4, c7_2328_5, c7_2328_6, c7_2328_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2327l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2327l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2327l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2327l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2327l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2329_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2327l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2329 :
    hubcapFit theRedpart rf7 p7_2327l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2329_1, c7_2329_2, c7_2329_3, c7_2329_4, c7_2329_5, c7_2329_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2326l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2326l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2326l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2331_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2326l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2331 :
    hubcapFit theRedpart rf7 p7_2326l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2331_1, c7_2331_2, c7_2331_3, c7_2331_4, c7_2331_5, c7_2331_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2325l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2325l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2325l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2325l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2332_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2325l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2332 :
    hubcapFit theRedpart rf7 p7_2325l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2332_1, c7_2332_2, c7_2332_3, c7_2332_4, c7_2332_5, c7_2332_6, c7_2332_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2322l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2322l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2322l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2322l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2334_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2334 :
    hubcapFit theRedpart rf7 p7_2322l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2334_1, c7_2334_2, c7_2334_3, c7_2334_4, c7_2334_5, c7_2334_6, c7_2334_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2320l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2320l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2320l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2320l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2320l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2336_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2320l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2336 :
    hubcapFit theRedpart rf7 p7_2320l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2336_1, c7_2336_2, c7_2336_3, c7_2336_4, c7_2336_5, c7_2336_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2339r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2339r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2339r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2339r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2339r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2340_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2339r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2340 :
    hubcapFit theRedpart rf7 p7_2339r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2340_1, c7_2340_2, c7_2340_3, c7_2340_4, c7_2340_5, c7_2340_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2341_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2339l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2341 :
    hubcapFit theRedpart rf7 p7_2339l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2341_1, c7_2341_2, c7_2341_3, c7_2341_4, c7_2341_5, c7_2341_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2343_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2338l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2343_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2338l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2343_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2338l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2343_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2338l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2343_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2338l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2343 :
    hubcapFit theRedpart rf7 p7_2338l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2343_1, c7_2343_2, c7_2343_3, c7_2343_4, c7_2343_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2356r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2356r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2356r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2356r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2356r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2357_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2356r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2357 :
    hubcapFit theRedpart rf7 p7_2356r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2357_1, c7_2357_2, c7_2357_3, c7_2357_4, c7_2357_5, c7_2357_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2358_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2356l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2358_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2356l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2358_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2356l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2358_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2356l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2358_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2356l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2358 :
    hubcapFit theRedpart rf7 p7_2356l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2358_1, c7_2358_2, c7_2358_3, c7_2358_4, c7_2358_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2355l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2355l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2355l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2355l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2360_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2355l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2360 :
    hubcapFit theRedpart rf7 p7_2355l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2360_1, c7_2360_2, c7_2360_3, c7_2360_4, c7_2360_5, c7_2360_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2362_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2353l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2362_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2353l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2362_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2353l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2362_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2353l) (hubSubn 7 6 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2362_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2353l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2362 :
    hubcapFit theRedpart rf7 p7_2353l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 2 6 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2362_1, c7_2362_2, c7_2362_3, c7_2362_4, c7_2362_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2363_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2363_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2363_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2352l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2363_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2352l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2363_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2352l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2363 :
    hubcapFit theRedpart rf7 p7_2352l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2363_1, c7_2363_2, c7_2363_3, c7_2363_4, c7_2363_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2366_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2365r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2366_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2365r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2366_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2365r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2366_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2365r) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2366_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2365r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2366 :
    hubcapFit theRedpart rf7 p7_2365r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2366_1, c7_2366_2, c7_2366_3, c7_2366_4, c7_2366_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2367_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2365l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2367_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2365l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2367_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2365l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2367_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2365l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2367_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2365l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2367 :
    hubcapFit theRedpart rf7 p7_2365l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2367_1, c7_2367_2, c7_2367_3, c7_2367_4, c7_2367_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2374r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2374r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2374r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2374r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2374r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2375_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2374r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2375 :
    hubcapFit theRedpart rf7 p7_2374r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2375_1, c7_2375_2, c7_2375_3, c7_2375_4, c7_2375_5, c7_2375_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2376_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2376_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2376_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2376_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2374l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2376_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2374l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2376 :
    hubcapFit theRedpart rf7 p7_2374l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2376_1, c7_2376_2, c7_2376_3, c7_2376_4, c7_2376_5]

end FourColor

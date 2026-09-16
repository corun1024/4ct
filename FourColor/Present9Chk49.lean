import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 49 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2340_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2340 :
    hubcapFit theRedpart rf9 p9_2335l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2340_1, c9_2340_2, c9_2340_3, c9_2340_4, c9_2340_5, c9_2340_6, c9_2340_7, c9_2340_8, c9_2340_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2334l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2334l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2342_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2342 :
    hubcapFit theRedpart rf9 p9_2334l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2342_1, c9_2342_2, c9_2342_3, c9_2342_4, c9_2342_5, c9_2342_6, c9_2342_7, c9_2342_8, c9_2342_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2344_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2344 :
    hubcapFit theRedpart rf9 p9_2332l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2344_1, c9_2344_2, c9_2344_3, c9_2344_4, c9_2344_5, c9_2344_6, c9_2344_7, c9_2344_8, c9_2344_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2330l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2330l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2330l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2346_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2330l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2346 :
    hubcapFit theRedpart rf9 p9_2330l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2346_1, c9_2346_2, c9_2346_3, c9_2346_4, c9_2346_5, c9_2346_6, c9_2346_7, c9_2346_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2329l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2329l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2329l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2348_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2348 :
    hubcapFit theRedpart rf9 p9_2329l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2348_1, c9_2348_2, c9_2348_3, c9_2348_4, c9_2348_5, c9_2348_6, c9_2348_7, c9_2348_8, c9_2348_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2328l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2328l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2328l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2350_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2350 :
    hubcapFit theRedpart rf9 p9_2328l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2350_1, c9_2350_2, c9_2350_3, c9_2350_4, c9_2350_5, c9_2350_6, c9_2350_7, c9_2350_8, c9_2350_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2352r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2353_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2352r) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2353 :
    hubcapFit theRedpart rf9 p9_2352r
    (Hubcap.one 0 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2353_1, c9_2353_2, c9_2353_3, c9_2353_4, c9_2353_5, c9_2353_6, c9_2353_7, c9_2353_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2354_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2354 :
    hubcapFit theRedpart rf9 p9_2352l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2354_1, c9_2354_2, c9_2354_3, c9_2354_4, c9_2354_5, c9_2354_6, c9_2354_7, c9_2354_8, c9_2354_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2326l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2326l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2326l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2356_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2326l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2356 :
    hubcapFit theRedpart rf9 p9_2326l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2356_1, c9_2356_2, c9_2356_3, c9_2356_4, c9_2356_5, c9_2356_6, c9_2356_7, c9_2356_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2325l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2325l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2325l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2358_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2325l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2358 :
    hubcapFit theRedpart rf9 p9_2325l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2358_1, c9_2358_2, c9_2358_3, c9_2358_4, c9_2358_5, c9_2358_6, c9_2358_7, c9_2358_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2365_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2364r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2365_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2364r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2365_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2364r) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2365_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2364r) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2365_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2364r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2365 :
    hubcapFit theRedpart rf9 p9_2364r
    (Hubcap.one 3 3 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2365_1, c9_2365_2, c9_2365_3, c9_2365_4, c9_2365_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2364l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2364l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2364l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2364l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2364l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2364l) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2366_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2364l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2366 :
    hubcapFit theRedpart rf9 p9_2364l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2366_1, c9_2366_2, c9_2366_3, c9_2366_4, c9_2366_5, c9_2366_6, c9_2366_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2363l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2363l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2363l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2363l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2363l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2363l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2368_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2363l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2368 :
    hubcapFit theRedpart rf9 p9_2363l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2368_1, c9_2368_2, c9_2368_3, c9_2368_4, c9_2368_5, c9_2368_6, c9_2368_7]

end FourColor

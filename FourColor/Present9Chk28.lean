import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 28 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1335l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1335l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1337_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1337 :
    hubcapFit theRedpart rf9 p9_1335l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1337_1, c9_1337_2, c9_1337_3, c9_1337_4, c9_1337_5, c9_1337_6, c9_1337_7, c9_1337_8, c9_1337_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1334l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1334l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1334l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1339_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1334l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1339 :
    hubcapFit theRedpart rf9 p9_1334l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1339_1, c9_1339_2, c9_1339_3, c9_1339_4, c9_1339_5, c9_1339_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1332l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1332l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1341_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1332l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1341 :
    hubcapFit theRedpart rf9 p9_1332l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1341_1, c9_1341_2, c9_1341_3, c9_1341_4, c9_1341_5, c9_1341_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1352r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1352r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1353_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1352r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1353 :
    hubcapFit theRedpart rf9 p9_1352r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1353_1, c9_1353_2, c9_1353_3, c9_1353_4, c9_1353_5, c9_1353_6, c9_1353_7, c9_1353_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1354_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1354 :
    hubcapFit theRedpart rf9 p9_1352l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1354_1, c9_1354_2, c9_1354_3, c9_1354_4, c9_1354_5, c9_1354_6, c9_1354_7, c9_1354_8, c9_1354_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1356_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1356 :
    hubcapFit theRedpart rf9 p9_1350l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1356_1, c9_1356_2, c9_1356_3, c9_1356_4, c9_1356_5, c9_1356_6, c9_1356_7, c9_1356_8, c9_1356_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1358_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1348l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1358 :
    hubcapFit theRedpart rf9 p9_1348l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1358_1, c9_1358_2, c9_1358_3, c9_1358_4, c9_1358_5, c9_1358_6, c9_1358_7, c9_1358_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1347l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1347l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1347l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1360_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1347l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1360 :
    hubcapFit theRedpart rf9 p9_1347l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1360_1, c9_1360_2, c9_1360_3, c9_1360_4, c9_1360_5, c9_1360_6, c9_1360_7, c9_1360_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1346l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1346l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1346l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1362_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1346l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1362 :
    hubcapFit theRedpart rf9 p9_1346l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1362_1, c9_1362_2, c9_1362_3, c9_1362_4, c9_1362_5, c9_1362_6, c9_1362_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1344l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1364_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1344l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1364 :
    hubcapFit theRedpart rf9 p9_1344l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1364_1, c9_1364_2, c9_1364_3, c9_1364_4, c9_1364_5, c9_1364_6, c9_1364_7, c9_1364_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1343l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1343l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1343l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1366_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1366 :
    hubcapFit theRedpart rf9 p9_1343l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1366_1, c9_1366_2, c9_1366_3, c9_1366_4, c9_1366_5, c9_1366_6, c9_1366_7, c9_1366_8, c9_1366_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1342l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1342l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1342l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1368_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1342l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1368 :
    hubcapFit theRedpart rf9 p9_1342l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1368_1, c9_1368_2, c9_1368_3, c9_1368_4, c9_1368_5, c9_1368_6, c9_1368_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1330l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1330l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1330l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1371_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1330l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1371 :
    hubcapFit theRedpart rf9 p9_1330l
    (Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1371_1, c9_1371_2, c9_1371_3, c9_1371_4, c9_1371_5, c9_1371_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1329l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1329l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1329l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1329l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1329l) (hubSubn 9 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1372_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1329l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1372 :
    hubcapFit theRedpart rf9 p9_1329l
    (Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1372_1, c9_1372_2, c9_1372_3, c9_1372_4, c9_1372_5, c9_1372_6, c9_1372_7, c9_1372_8]

end FourColor

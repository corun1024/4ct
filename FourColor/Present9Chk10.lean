import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 10 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_419l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_419l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_419l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_419l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_419l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_442_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_419l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_442 :
    hubcapFit theRedpart rf9 p9_419l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_442_1, c9_442_2, c9_442_3, c9_442_4, c9_442_5, c9_442_6, c9_442_7, c9_442_8, c9_442_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_418l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_418l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_418l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_418l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_418l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_444_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_418l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_444 :
    hubcapFit theRedpart rf9 p9_418l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_444_1, c9_444_2, c9_444_3, c9_444_4, c9_444_5, c9_444_6, c9_444_7, c9_444_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_417l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_446_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_417l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_446 :
    hubcapFit theRedpart rf9 p9_417l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_446_1, c9_446_2, c9_446_3, c9_446_4, c9_446_5, c9_446_6, c9_446_7, c9_446_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_459r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_459r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_459r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_459r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_459r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_459r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_459r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_460_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_459r) (hubSubn 9 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_460 :
    hubcapFit theRedpart rf9 p9_459r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_460_1, c9_460_2, c9_460_3, c9_460_4, c9_460_5, c9_460_6, c9_460_7, c9_460_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_459l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_459l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_459l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_459l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_459l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_459l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_461_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_461 :
    hubcapFit theRedpart rf9 p9_459l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_461_1, c9_461_2, c9_461_3, c9_461_4, c9_461_5, c9_461_6, c9_461_7, c9_461_8, c9_461_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_457l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_457l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_457l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_457l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_463_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_457l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_463 :
    hubcapFit theRedpart rf9 p9_457l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_463_1, c9_463_2, c9_463_3, c9_463_4, c9_463_5, c9_463_6, c9_463_7, c9_463_8, c9_463_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_455l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_455l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_455l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_455l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_455l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_455l) (hubSubn 9 8 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_465_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_455l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_465 :
    hubcapFit theRedpart rf9 p9_455l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 3 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_465_1, c9_465_2, c9_465_3, c9_465_4, c9_465_5, c9_465_6, c9_465_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_453l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_467_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_453l) (hubSubn 9 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_467 :
    hubcapFit theRedpart rf9 p9_453l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_467_1, c9_467_2, c9_467_3, c9_467_4, c9_467_5, c9_467_6, c9_467_7, c9_467_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_452l) (hubSubn 9 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_452l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_469_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_452l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_469 :
    hubcapFit theRedpart rf9 p9_452l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 5 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_469_1, c9_469_2, c9_469_3, c9_469_4, c9_469_5, c9_469_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_451l) (hubSubn 9 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_451l) (hubSubn 9 8 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_470_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_451l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_470 :
    hubcapFit theRedpart rf9 p9_451l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.two 1 5 6 <|
     Hubcap.two 3 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_470_1, c9_470_2, c9_470_3, c9_470_4, c9_470_5, c9_470_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_472_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_472_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_450l) (hubSubn 9 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_472_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_450l) (hubSubn 9 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_472_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_450l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_472_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_450l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_472 :
    hubcapFit theRedpart rf9 p9_450l
    (Hubcap.one 0 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_472_1, c9_472_2, c9_472_3, c9_472_4, c9_472_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_449l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_449l) (hubSubn 9 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_449l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_473_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_449l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_473 :
    hubcapFit theRedpart rf9 p9_449l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_473_1, c9_473_2, c9_473_3, c9_473_4, c9_473_5, c9_473_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_478r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_478r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_478r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_478r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_478r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_478r) (hubSubn 9 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_479_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_478r) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_479 :
    hubcapFit theRedpart rf9 p9_478r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_479_1, c9_479_2, c9_479_3, c9_479_4, c9_479_5, c9_479_6, c9_479_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_478l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_478l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_478l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_478l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_480_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_480 :
    hubcapFit theRedpart rf9 p9_478l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_480_1, c9_480_2, c9_480_3, c9_480_4, c9_480_5, c9_480_6, c9_480_7, c9_480_8, c9_480_9]

end FourColor

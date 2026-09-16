import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 20 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_827l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_827l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_827l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_827l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_827l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_914_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_827l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_914 :
    hubcapFit theRedpart rf9 p9_827l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_914_1, c9_914_2, c9_914_3, c9_914_4, c9_914_5, c9_914_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_942r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_942r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_942r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_942r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_942r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_942r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_942r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_942r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_943_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_942r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_943 :
    hubcapFit theRedpart rf9 p9_942r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_943_1, c9_943_2, c9_943_3, c9_943_4, c9_943_5, c9_943_6, c9_943_7, c9_943_8, c9_943_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_942l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_942l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_942l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_942l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_944_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_944 :
    hubcapFit theRedpart rf9 p9_942l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_944_1, c9_944_2, c9_944_3, c9_944_4, c9_944_5, c9_944_6, c9_944_7, c9_944_8, c9_944_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_940l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_940l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_940l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_940l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_946_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_946 :
    hubcapFit theRedpart rf9 p9_940l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_946_1, c9_946_2, c9_946_3, c9_946_4, c9_946_5, c9_946_6, c9_946_7, c9_946_8, c9_946_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_939l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_939l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_948_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_939l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_948 :
    hubcapFit theRedpart rf9 p9_939l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_948_1, c9_948_2, c9_948_3, c9_948_4, c9_948_5, c9_948_6, c9_948_7, c9_948_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_936l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_950_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_936l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_950 :
    hubcapFit theRedpart rf9 p9_936l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_950_1, c9_950_2, c9_950_3, c9_950_4, c9_950_5, c9_950_6, c9_950_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_952_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_934l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_952 :
    hubcapFit theRedpart rf9 p9_934l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_952_1, c9_952_2, c9_952_3, c9_952_4, c9_952_5, c9_952_6, c9_952_7, c9_952_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_932l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_932l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_932l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_932l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_954_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_932l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_954 :
    hubcapFit theRedpart rf9 p9_932l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_954_1, c9_954_2, c9_954_3, c9_954_4, c9_954_5, c9_954_6, c9_954_7, c9_954_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_931l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_931l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_931l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_931l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_931l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_931l) (hubSubn 9 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_956_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_931l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_956 :
    hubcapFit theRedpart rf9 p9_931l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_956_1, c9_956_2, c9_956_3, c9_956_4, c9_956_5, c9_956_6, c9_956_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_969r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_969r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_969r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_969r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_969r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_969r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_969r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_970_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_969r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_970 :
    hubcapFit theRedpart rf9 p9_969r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_970_1, c9_970_2, c9_970_3, c9_970_4, c9_970_5, c9_970_6, c9_970_7, c9_970_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_969l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_971_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_969l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_971 :
    hubcapFit theRedpart rf9 p9_969l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_971_1, c9_971_2, c9_971_3, c9_971_4, c9_971_5, c9_971_6, c9_971_7, c9_971_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_973_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_973 :
    hubcapFit theRedpart rf9 p9_967l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_973_1, c9_973_2, c9_973_3, c9_973_4, c9_973_5, c9_973_6, c9_973_7, c9_973_8, c9_973_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_975_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_965l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_975 :
    hubcapFit theRedpart rf9 p9_965l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_975_1, c9_975_2, c9_975_3, c9_975_4, c9_975_5, c9_975_6, c9_975_7, c9_975_8]

end FourColor

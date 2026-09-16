import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 99 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4906l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4906l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4906l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4906l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4906l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4932_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4906l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4932 :
    hubcapFit theRedpart rf8 p8_4906l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4932_1, c8_4932_2, c8_4932_3, c8_4932_4, c8_4932_5, c8_4932_6, c8_4932_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4944r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4944r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4944r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4944r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4944r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4944r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4944r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4945_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4944r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4945 :
    hubcapFit theRedpart rf8 p8_4944r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4945_1, c8_4945_2, c8_4945_3, c8_4945_4, c8_4945_5, c8_4945_6, c8_4945_7, c8_4945_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4944l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4944l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4944l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4944l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4944l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4944l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4946_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4944l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4946 :
    hubcapFit theRedpart rf8 p8_4944l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4946_1, c8_4946_2, c8_4946_3, c8_4946_4, c8_4946_5, c8_4946_6, c8_4946_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4949r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4949r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4949r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4949r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4949r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4949r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4950_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4949r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4950 :
    hubcapFit theRedpart rf8 p8_4949r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4950_1, c8_4950_2, c8_4950_3, c8_4950_4, c8_4950_5, c8_4950_6, c8_4950_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4949l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4949l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4949l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4949l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4951_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4949l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4951 :
    hubcapFit theRedpart rf8 p8_4949l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4951_1, c8_4951_2, c8_4951_3, c8_4951_4, c8_4951_5, c8_4951_6, c8_4951_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4948l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4948l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4948l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4948l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4948l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4948l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4953_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4948l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4953 :
    hubcapFit theRedpart rf8 p8_4948l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4953_1, c8_4953_2, c8_4953_3, c8_4953_4, c8_4953_5, c8_4953_6, c8_4953_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4962r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4962r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4962r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4962r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4962r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4962r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4962r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4963_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4962r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4963 :
    hubcapFit theRedpart rf8 p8_4962r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4963_1, c8_4963_2, c8_4963_3, c8_4963_4, c8_4963_5, c8_4963_6, c8_4963_7, c8_4963_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4962l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4962l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4964_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4964 :
    hubcapFit theRedpart rf8 p8_4962l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4964_1, c8_4964_2, c8_4964_3, c8_4964_4, c8_4964_5, c8_4964_6, c8_4964_7, c8_4964_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4961l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4961l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4961l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4966_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4961l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4966 :
    hubcapFit theRedpart rf8 p8_4961l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4966_1, c8_4966_2, c8_4966_3, c8_4966_4, c8_4966_5, c8_4966_6, c8_4966_7, c8_4966_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4960l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4960l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4960l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4968_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4968 :
    hubcapFit theRedpart rf8 p8_4960l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4968_1, c8_4968_2, c8_4968_3, c8_4968_4, c8_4968_5, c8_4968_6, c8_4968_7, c8_4968_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4959l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4970_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4959l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4970 :
    hubcapFit theRedpart rf8 p8_4959l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4970_1, c8_4970_2, c8_4970_3, c8_4970_4, c8_4970_5, c8_4970_6, c8_4970_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4972_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4972 :
    hubcapFit theRedpart rf8 p8_4958l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4972_1, c8_4972_2, c8_4972_3, c8_4972_4, c8_4972_5, c8_4972_6, c8_4972_7, c8_4972_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4957l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4957l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4957l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4974_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4957l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4974 :
    hubcapFit theRedpart rf8 p8_4957l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4974_1, c8_4974_2, c8_4974_3, c8_4974_4, c8_4974_5, c8_4974_6, c8_4974_7, c8_4974_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4956l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4956l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4956l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4956l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4976_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4956l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4976 :
    hubcapFit theRedpart rf8 p8_4956l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4976_1, c8_4976_2, c8_4976_3, c8_4976_4, c8_4976_5, c8_4976_6, c8_4976_7]

end FourColor

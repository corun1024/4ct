import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 74 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3982_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3981r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3982_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3981r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3982_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3981r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3982_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3981r) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3982_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3981r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3982 :
    hubcapFit theRedpart rf7 p7_3981r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3982_1, c7_3982_2, c7_3982_3, c7_3982_4, c7_3982_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3981l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3981l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3981l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3981l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3981l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3981l) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3983_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3981l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3983 :
    hubcapFit theRedpart rf7 p7_3981l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3983_1, c7_3983_2, c7_3983_3, c7_3983_4, c7_3983_5, c7_3983_6, c7_3983_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3978l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3978l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3978l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3978l) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3985_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3978l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3985 :
    hubcapFit theRedpart rf7 p7_3978l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3985_1, c7_3985_2, c7_3985_3, c7_3985_4, c7_3985_5, c7_3985_6, c7_3985_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3977l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3977l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3987_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3977l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3987 :
    hubcapFit theRedpart rf7 p7_3977l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3987_1, c7_3987_2, c7_3987_3, c7_3987_4, c7_3987_5, c7_3987_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3989_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3960l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3989_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3960l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3989_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3960l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3989_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3960l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3989_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3960l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3989 :
    hubcapFit theRedpart rf7 p7_3960l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3989_1, c7_3989_2, c7_3989_3, c7_3989_4, c7_3989_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3959l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3959l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3990_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3959l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3990 :
    hubcapFit theRedpart rf7 p7_3959l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3990_1, c7_3990_2, c7_3990_3, c7_3990_4, c7_3990_5, c7_3990_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3992_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3958l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3992 :
    hubcapFit theRedpart rf7 p7_3958l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3992_1, c7_3992_2, c7_3992_3, c7_3992_4, c7_3992_5, c7_3992_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3804l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3804l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3804l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3804l) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3994_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3804l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3994 :
    hubcapFit theRedpart rf7 p7_3804l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3994_1, c7_3994_2, c7_3994_3, c7_3994_4, c7_3994_5, c7_3994_6, c7_3994_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4011r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4011r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4011r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4011r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4011r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4012_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4011r) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4012 :
    hubcapFit theRedpart rf7 p7_4011r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4012_1, c7_4012_2, c7_4012_3, c7_4012_4, c7_4012_5, c7_4012_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4011l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4011l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4011l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4011l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4011l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4013_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4011l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4013 :
    hubcapFit theRedpart rf7 p7_4011l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4013_1, c7_4013_2, c7_4013_3, c7_4013_4, c7_4013_5, c7_4013_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4010l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4010l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4015_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4010l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4015 :
    hubcapFit theRedpart rf7 p7_4010l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4015_1, c7_4015_2, c7_4015_3, c7_4015_4, c7_4015_5, c7_4015_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4009l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4009l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4009l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4009l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4009l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4009l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4016_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4009l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4016 :
    hubcapFit theRedpart rf7 p7_4009l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4016_1, c7_4016_2, c7_4016_3, c7_4016_4, c7_4016_5, c7_4016_6, c7_4016_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4021r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4021r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4021r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4021r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4021r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4022_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4021r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4022 :
    hubcapFit theRedpart rf7 p7_4021r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4022_1, c7_4022_2, c7_4022_3, c7_4022_4, c7_4022_5, c7_4022_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4021l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4021l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4021l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4021l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4021l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4023_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4021l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4023 :
    hubcapFit theRedpart rf7 p7_4021l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4023_1, c7_4023_2, c7_4023_3, c7_4023_4, c7_4023_5, c7_4023_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4020l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4020l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4020l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4020l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4020l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4025_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4020l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4025 :
    hubcapFit theRedpart rf7 p7_4020l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4025_1, c7_4025_2, c7_4025_3, c7_4025_4, c7_4025_5, c7_4025_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4019l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4019l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4019l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4026_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4019l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4026 :
    hubcapFit theRedpart rf7 p7_4019l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4026_1, c7_4026_2, c7_4026_3, c7_4026_4, c7_4026_5, c7_4026_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4018l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4018l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4028_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4018l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4028 :
    hubcapFit theRedpart rf7 p7_4018l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4028_1, c7_4028_2, c7_4028_3, c7_4028_4, c7_4028_5, c7_4028_6]

end FourColor

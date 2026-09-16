import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 79 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3977_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3969l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3977 :
    hubcapFit theRedpart rf8 p8_3969l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3977_1, c8_3977_2, c8_3977_3, c8_3977_4, c8_3977_5, c8_3977_6, c8_3977_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3968l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3968l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3968l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3979_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3968l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3979 :
    hubcapFit theRedpart rf8 p8_3968l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3979_1, c8_3979_2, c8_3979_3, c8_3979_4, c8_3979_5, c8_3979_6, c8_3979_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3967l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3967l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3981_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3967l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3981 :
    hubcapFit theRedpart rf8 p8_3967l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3981_1, c8_3981_2, c8_3981_3, c8_3981_4, c8_3981_5, c8_3981_6, c8_3981_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3966l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3966l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3966l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3983_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3966l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3983 :
    hubcapFit theRedpart rf8 p8_3966l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3983_1, c8_3983_2, c8_3983_3, c8_3983_4, c8_3983_5, c8_3983_6, c8_3983_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3965l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3985_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3965l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3985 :
    hubcapFit theRedpart rf8 p8_3965l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3985_1, c8_3985_2, c8_3985_3, c8_3985_4, c8_3985_5, c8_3985_6, c8_3985_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3964l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3964l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3964l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3987_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3987 :
    hubcapFit theRedpart rf8 p8_3964l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3987_1, c8_3987_2, c8_3987_3, c8_3987_4, c8_3987_5, c8_3987_6, c8_3987_7, c8_3987_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3963l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3963l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3989_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3963l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3989 :
    hubcapFit theRedpart rf8 p8_3963l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3989_1, c8_3989_2, c8_3989_3, c8_3989_4, c8_3989_5, c8_3989_6, c8_3989_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3961l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3961l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3961l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3961l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3961l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3961l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3991_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3961l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3991 :
    hubcapFit theRedpart rf8 p8_3961l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3991_1, c8_3991_2, c8_3991_3, c8_3991_4, c8_3991_5, c8_3991_6, c8_3991_7, c8_3991_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3960l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3960l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3993_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3960l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3993 :
    hubcapFit theRedpart rf8 p8_3960l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3993_1, c8_3993_2, c8_3993_3, c8_3993_4, c8_3993_5, c8_3993_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3959l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3959l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3994_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3959l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3994 :
    hubcapFit theRedpart rf8 p8_3959l
    (Hubcap.one 2 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3994_1, c8_3994_2, c8_3994_3, c8_3994_4, c8_3994_5, c8_3994_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3958l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3958l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3996_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3958l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3996 :
    hubcapFit theRedpart rf8 p8_3958l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3996_1, c8_3996_2, c8_3996_3, c8_3996_4, c8_3996_5, c8_3996_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3924l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3924l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3924l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3998_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3924l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3998 :
    hubcapFit theRedpart rf8 p8_3924l
    (Hubcap.one 2 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3998_1, c8_3998_2, c8_3998_3, c8_3998_4, c8_3998_5, c8_3998_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4010r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4010r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4010r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4011_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4010r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4011 :
    hubcapFit theRedpart rf8 p8_4010r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4011_1, c8_4011_2, c8_4011_3, c8_4011_4, c8_4011_5, c8_4011_6, c8_4011_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4010l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4010l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4010l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4012_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4010l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4012 :
    hubcapFit theRedpart rf8 p8_4010l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4012_1, c8_4012_2, c8_4012_3, c8_4012_4, c8_4012_5, c8_4012_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4009l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4009l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4009l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4009l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4009l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4014_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4009l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4014 :
    hubcapFit theRedpart rf8 p8_4009l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4014_1, c8_4014_2, c8_4014_3, c8_4014_4, c8_4014_5, c8_4014_6, c8_4014_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4008l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4008l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4008l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4008l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4016_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4008l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4016 :
    hubcapFit theRedpart rf8 p8_4008l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4016_1, c8_4016_2, c8_4016_3, c8_4016_4, c8_4016_5, c8_4016_6, c8_4016_7]

end FourColor

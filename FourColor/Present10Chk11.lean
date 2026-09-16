import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 11 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_461l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_461l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_461l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_461l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_461l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_520_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_520 :
    hubcapFit theRedpart rf10 p10_461l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_520_1, c10_520_2, c10_520_3, c10_520_4, c10_520_5, c10_520_6, c10_520_7, c10_520_8, c10_520_9, c10_520_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_460l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_460l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_460l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_460l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_460l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_460l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_460l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_460l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_460l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_522_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_460l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_522 :
    hubcapFit theRedpart rf10 p10_460l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_522_1, c10_522_2, c10_522_3, c10_522_4, c10_522_5, c10_522_6, c10_522_7, c10_522_8, c10_522_9, c10_522_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_525l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_525l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_525l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_526_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_525l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_526 :
    hubcapFit theRedpart rf10 p10_525l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_526_1, c10_526_2, c10_526_3, c10_526_4, c10_526_5, c10_526_6, c10_526_7, c10_526_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_528l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_528l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_528l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_529_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_528l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_529 :
    hubcapFit theRedpart rf10 p10_528l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_529_1, c10_529_2, c10_529_3, c10_529_4, c10_529_5, c10_529_6, c10_529_7, c10_529_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_528r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_528r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_528r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_528r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_528r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_528r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_528r) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_531_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_528r) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_531 :
    hubcapFit theRedpart rf10 p10_528r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_531_1, c10_531_2, c10_531_3, c10_531_4, c10_531_5, c10_531_6, c10_531_7, c10_531_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_458l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_458l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_458l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_458l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_458l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_535_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_458l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_535 :
    hubcapFit theRedpart rf10 p10_458l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_535_1, c10_535_2, c10_535_3, c10_535_4, c10_535_5, c10_535_6, c10_535_7, c10_535_8, c10_535_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_562r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_562r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_562r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_563_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_562r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_563 :
    hubcapFit theRedpart rf10 p10_562r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_563_1, c10_563_2, c10_563_3, c10_563_4, c10_563_5, c10_563_6, c10_563_7, c10_563_8, c10_563_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_564_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_562l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_564 :
    hubcapFit theRedpart rf10 p10_562l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_564_1, c10_564_2, c10_564_3, c10_564_4, c10_564_5, c10_564_6, c10_564_7, c10_564_8, c10_564_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_561l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_561l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_561l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_566_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_561l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_566 :
    hubcapFit theRedpart rf10 p10_561l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_566_1, c10_566_2, c10_566_3, c10_566_4, c10_566_5, c10_566_6, c10_566_7, c10_566_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_559l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_559l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_568_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_559l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_568 :
    hubcapFit theRedpart rf10 p10_559l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_568_1, c10_568_2, c10_568_3, c10_568_4, c10_568_5, c10_568_6, c10_568_7, c10_568_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_558l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_558l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_558l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_570_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_558l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_570 :
    hubcapFit theRedpart rf10 p10_558l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_570_1, c10_570_2, c10_570_3, c10_570_4, c10_570_5, c10_570_6, c10_570_7, c10_570_8, c10_570_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_551l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_551l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_551l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_572_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_551l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_572 :
    hubcapFit theRedpart rf10 p10_551l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_572_1, c10_572_2, c10_572_3, c10_572_4, c10_572_5, c10_572_6, c10_572_7, c10_572_8]

end FourColor

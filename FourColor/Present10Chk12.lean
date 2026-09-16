import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 12 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_550l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_550l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_550l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_550l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_574_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_550l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_574 :
    hubcapFit theRedpart rf10 p10_550l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.two 3 4 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_574_1, c10_574_2, c10_574_3, c10_574_4, c10_574_5, c10_574_6, c10_574_7, c10_574_8, c10_574_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_548l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_548l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_548l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_576_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_548l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_576 :
    hubcapFit theRedpart rf10 p10_548l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_576_1, c10_576_2, c10_576_3, c10_576_4, c10_576_5, c10_576_6, c10_576_7, c10_576_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_546l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_546l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_546l) (hubSubn 10 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_578_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_546l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_578 :
    hubcapFit theRedpart rf10 p10_546l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_578_1, c10_578_2, c10_578_3, c10_578_4, c10_578_5, c10_578_6, c10_578_7, c10_578_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_545l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_545l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_545l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_545l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_580_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_545l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_580 :
    hubcapFit theRedpart rf10 p10_545l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_580_1, c10_580_2, c10_580_3, c10_580_4, c10_580_5, c10_580_6, c10_580_7, c10_580_8, c10_580_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_543l) (hubSubn 10 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_582_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_543l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_582 :
    hubcapFit theRedpart rf10 p10_543l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_582_1, c10_582_2, c10_582_3, c10_582_4, c10_582_5, c10_582_6, c10_582_7, c10_582_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_542l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_584_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_542l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_584 :
    hubcapFit theRedpart rf10 p10_542l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_584_1, c10_584_2, c10_584_3, c10_584_4, c10_584_5, c10_584_6, c10_584_7, c10_584_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_541l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_541l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_541l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_586_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_541l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_586 :
    hubcapFit theRedpart rf10 p10_541l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_586_1, c10_586_2, c10_586_3, c10_586_4, c10_586_5, c10_586_6, c10_586_7, c10_586_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_540l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_540l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_540l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_540l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_540l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_540l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_540l) (hubSubn 10 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_588_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_540l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_588 :
    hubcapFit theRedpart rf10 p10_540l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_588_1, c10_588_2, c10_588_3, c10_588_4, c10_588_5, c10_588_6, c10_588_7, c10_588_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_539l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_539l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_539l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_539l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_539l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_539l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_539l) (hubSubn 10 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_590_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_539l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_590 :
    hubcapFit theRedpart rf10 p10_539l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_590_1, c10_590_2, c10_590_3, c10_590_4, c10_590_5, c10_590_6, c10_590_7, c10_590_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_602r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_602r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_602r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_602r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_602r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_602r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_602r) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_603_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_602r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_603 :
    hubcapFit theRedpart rf10 p10_602r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_603_1, c10_603_2, c10_603_3, c10_603_4, c10_603_5, c10_603_6, c10_603_7, c10_603_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_602l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_602l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_604_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_602l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_604 :
    hubcapFit theRedpart rf10 p10_602l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_604_1, c10_604_2, c10_604_3, c10_604_4, c10_604_5, c10_604_6, c10_604_7, c10_604_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_606_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_600l) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_606 :
    hubcapFit theRedpart rf10 p10_600l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_606_1, c10_606_2, c10_606_3, c10_606_4, c10_606_5, c10_606_6, c10_606_7, c10_606_8, c10_606_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_598l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_598l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_598l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_608_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_598l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_608 :
    hubcapFit theRedpart rf10 p10_598l
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
  simp [hubcapFit, c10_608_1, c10_608_2, c10_608_3, c10_608_4, c10_608_5, c10_608_6, c10_608_7, c10_608_8, c10_608_9]

end FourColor

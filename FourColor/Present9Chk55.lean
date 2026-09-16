import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 55 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2550l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2550l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2608_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2608 :
    hubcapFit theRedpart rf9 p9_2550l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2608_1, c9_2608_2, c9_2608_3, c9_2608_4, c9_2608_5, c9_2608_6, c9_2608_7, c9_2608_8, c9_2608_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2549l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2549l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2549l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2549l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2549l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2549l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2610_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2549l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2610 :
    hubcapFit theRedpart rf9 p9_2549l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2610_1, c9_2610_2, c9_2610_3, c9_2610_4, c9_2610_5, c9_2610_6, c9_2610_7, c9_2610_8, c9_2610_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2548l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2548l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2548l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2548l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2612_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2548l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2612 :
    hubcapFit theRedpart rf9 p9_2548l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2612_1, c9_2612_2, c9_2612_3, c9_2612_4, c9_2612_5, c9_2612_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2547l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2547l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2547l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2547l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2547l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2613_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2547l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2613 :
    hubcapFit theRedpart rf9 p9_2547l
    (Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2613_1, c9_2613_2, c9_2613_3, c9_2613_4, c9_2613_5, c9_2613_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2634r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2634r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2634r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2634r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2634r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2634r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2635_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2634r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2635 :
    hubcapFit theRedpart rf9 p9_2634r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2635_1, c9_2635_2, c9_2635_3, c9_2635_4, c9_2635_5, c9_2635_6, c9_2635_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2634l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2634l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2634l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2634l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2634l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2634l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2634l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2636_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2634l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2636 :
    hubcapFit theRedpart rf9 p9_2634l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2636_1, c9_2636_2, c9_2636_3, c9_2636_4, c9_2636_5, c9_2636_6, c9_2636_7, c9_2636_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2633l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2633l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2633l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2633l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2633l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2633l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2638_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2633l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2638 :
    hubcapFit theRedpart rf9 p9_2633l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2638_1, c9_2638_2, c9_2638_3, c9_2638_4, c9_2638_5, c9_2638_6, c9_2638_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2630l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2640_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2630l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2640 :
    hubcapFit theRedpart rf9 p9_2630l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2640_1, c9_2640_2, c9_2640_3, c9_2640_4, c9_2640_5, c9_2640_6, c9_2640_7, c9_2640_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2648r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2648r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2648r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2648r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2648r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2648r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2649_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2648r) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2649 :
    hubcapFit theRedpart rf9 p9_2648r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2649_1, c9_2649_2, c9_2649_3, c9_2649_4, c9_2649_5, c9_2649_6, c9_2649_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2648l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2648l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2650_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2648l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2650 :
    hubcapFit theRedpart rf9 p9_2648l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2650_1, c9_2650_2, c9_2650_3, c9_2650_4, c9_2650_5, c9_2650_6, c9_2650_7, c9_2650_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2647l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2647l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2652_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2647l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2652 :
    hubcapFit theRedpart rf9 p9_2647l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2652_1, c9_2652_2, c9_2652_3, c9_2652_4, c9_2652_5, c9_2652_6, c9_2652_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2645l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2645l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2645l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2645l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2645l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2645l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2654_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2645l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2654 :
    hubcapFit theRedpart rf9 p9_2645l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2654_1, c9_2654_2, c9_2654_3, c9_2654_4, c9_2654_5, c9_2654_6, c9_2654_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2642l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2642l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2642l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2656_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2642l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2656 :
    hubcapFit theRedpart rf9 p9_2642l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2656_1, c9_2656_2, c9_2656_3, c9_2656_4, c9_2656_5, c9_2656_6, c9_2656_7, c9_2656_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2625l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2625l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2625l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2659_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2625l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2659 :
    hubcapFit theRedpart rf9 p9_2625l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2659_1, c9_2659_2, c9_2659_3, c9_2659_4, c9_2659_5, c9_2659_6, c9_2659_7]

end FourColor

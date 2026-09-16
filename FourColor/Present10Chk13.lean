import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 13 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_597l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_597l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_610_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_597l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_610 :
    hubcapFit theRedpart rf10 p10_597l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_610_1, c10_610_2, c10_610_3, c10_610_4, c10_610_5, c10_610_6, c10_610_7, c10_610_8, c10_610_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_596l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_596l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_596l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_596l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_596l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_596l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_596l) (hubSubn 10 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_612_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_596l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_612 :
    hubcapFit theRedpart rf10 p10_596l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 4 7 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_612_1, c10_612_2, c10_612_3, c10_612_4, c10_612_5, c10_612_6, c10_612_7, c10_612_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_595l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_595l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_595l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_614_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_595l) (hubSubn 10 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_614 :
    hubcapFit theRedpart rf10 p10_595l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_614_1, c10_614_2, c10_614_3, c10_614_4, c10_614_5, c10_614_6, c10_614_7, c10_614_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_594l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_594l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_594l) (hubSubn 10 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_616_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_594l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_616 :
    hubcapFit theRedpart rf10 p10_594l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_616_1, c10_616_2, c10_616_3, c10_616_4, c10_616_5, c10_616_6, c10_616_7, c10_616_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_593l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_593l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_618_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_593l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_618 :
    hubcapFit theRedpart rf10 p10_593l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_618_1, c10_618_2, c10_618_3, c10_618_4, c10_618_5, c10_618_6, c10_618_7, c10_618_8, c10_618_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_592l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_592l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_620_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_592l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_620 :
    hubcapFit theRedpart rf10 p10_592l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_620_1, c10_620_2, c10_620_3, c10_620_4, c10_620_5, c10_620_6, c10_620_7, c10_620_8, c10_620_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_626r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_626r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_626r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_626r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_626r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_626r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_626r) (hubSubn 10 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_627_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_626r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_627 :
    hubcapFit theRedpart rf10 p10_626r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_627_1, c10_627_2, c10_627_3, c10_627_4, c10_627_5, c10_627_6, c10_627_7, c10_627_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_640r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_640r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_640r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_640r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_640r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_640r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_640r) (hubSubn 10 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_641_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_640r) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_641 :
    hubcapFit theRedpart rf10 p10_640r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_641_1, c10_641_2, c10_641_3, c10_641_4, c10_641_5, c10_641_6, c10_641_7, c10_641_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_640l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_640l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_642_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_640l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_642 :
    hubcapFit theRedpart rf10 p10_640l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_642_1, c10_642_2, c10_642_3, c10_642_4, c10_642_5, c10_642_6, c10_642_7, c10_642_8, c10_642_9, c10_642_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_638l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_645_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_638l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_645 :
    hubcapFit theRedpart rf10 p10_638l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_645_1, c10_645_2, c10_645_3, c10_645_4, c10_645_5, c10_645_6, c10_645_7, c10_645_8, c10_645_9, c10_645_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_637l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_637l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_637l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_637l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_647_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_637l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_647 :
    hubcapFit theRedpart rf10 p10_637l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_647_1, c10_647_2, c10_647_3, c10_647_4, c10_647_5, c10_647_6, c10_647_7, c10_647_8, c10_647_9, c10_647_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_636l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_636l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_636l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_636l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_636l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_636l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_636l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_636l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_649_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_636l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_649 :
    hubcapFit theRedpart rf10 p10_636l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_649_1, c10_649_2, c10_649_3, c10_649_4, c10_649_5, c10_649_6, c10_649_7, c10_649_8, c10_649_9]

end FourColor

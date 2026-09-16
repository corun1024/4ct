import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 99 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5259l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5259l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5259l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5265_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5259l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5265 :
    hubcapFit theRedpart rf7 p7_5259l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5265_1, c7_5265_2, c7_5265_3, c7_5265_4, c7_5265_5, c7_5265_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5267r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5267r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5267r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5267r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5267r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5268_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5267r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5268 :
    hubcapFit theRedpart rf7 p7_5267r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5268_1, c7_5268_2, c7_5268_3, c7_5268_4, c7_5268_5, c7_5268_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5273r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5273r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5273r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5273r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5274_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5273r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5274 :
    hubcapFit theRedpart rf7 p7_5273r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5274_1, c7_5274_2, c7_5274_3, c7_5274_4, c7_5274_5, c7_5274_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5271l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5271l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5271l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5271l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5271l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5276_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5271l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5276 :
    hubcapFit theRedpart rf7 p7_5271l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5276_1, c7_5276_2, c7_5276_3, c7_5276_4, c7_5276_5, c7_5276_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5286r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5286r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5286r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5286r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5286r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5287_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5286r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5287 :
    hubcapFit theRedpart rf7 p7_5286r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5287_1, c7_5287_2, c7_5287_3, c7_5287_4, c7_5287_5, c7_5287_6, c7_5287_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5286l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5286l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5286l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5286l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5288_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5286l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5288 :
    hubcapFit theRedpart rf7 p7_5286l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5288_1, c7_5288_2, c7_5288_3, c7_5288_4, c7_5288_5, c7_5288_6, c7_5288_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5284l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5284l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5284l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5284l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5284l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5284l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5290_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5284l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5290 :
    hubcapFit theRedpart rf7 p7_5284l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5290_1, c7_5290_2, c7_5290_3, c7_5290_4, c7_5290_5, c7_5290_6, c7_5290_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5281l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5281l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5292_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5281l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5292 :
    hubcapFit theRedpart rf7 p7_5281l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5292_1, c7_5292_2, c7_5292_3, c7_5292_4, c7_5292_5, c7_5292_6, c7_5292_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5279l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5279l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5279l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5294_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5279l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5294 :
    hubcapFit theRedpart rf7 p7_5279l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5294_1, c7_5294_2, c7_5294_3, c7_5294_4, c7_5294_5, c7_5294_6, c7_5294_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5278l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5278l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5278l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5278l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5278l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5278l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5296_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5278l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5296 :
    hubcapFit theRedpart rf7 p7_5278l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5296_1, c7_5296_2, c7_5296_3, c7_5296_4, c7_5296_5, c7_5296_6, c7_5296_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5307r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5307r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5307r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5308_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5307r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5308 :
    hubcapFit theRedpart rf7 p7_5307r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5308_1, c7_5308_2, c7_5308_3, c7_5308_4, c7_5308_5, c7_5308_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5307l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5307l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5307l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5309_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5307l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5309 :
    hubcapFit theRedpart rf7 p7_5307l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5309_1, c7_5309_2, c7_5309_3, c7_5309_4, c7_5309_5, c7_5309_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5305l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5305l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5305l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5305l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5305l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5311_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5305l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5311 :
    hubcapFit theRedpart rf7 p7_5305l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5311_1, c7_5311_2, c7_5311_3, c7_5311_4, c7_5311_5, c7_5311_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5304l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5304l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5304l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5304l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5304l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5313_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5304l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5313 :
    hubcapFit theRedpart rf7 p7_5304l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5313_1, c7_5313_2, c7_5313_3, c7_5313_4, c7_5313_5, c7_5313_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5303l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5303l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5303l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5303l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5303l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5314_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5303l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5314 :
    hubcapFit theRedpart rf7 p7_5303l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5314_1, c7_5314_2, c7_5314_3, c7_5314_4, c7_5314_5, c7_5314_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5302l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5302l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5302l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5316_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5302l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5316 :
    hubcapFit theRedpart rf7 p7_5302l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5316_1, c7_5316_2, c7_5316_3, c7_5316_4, c7_5316_5, c7_5316_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5300l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5300l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5300l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5318_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5300l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5318 :
    hubcapFit theRedpart rf7 p7_5300l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5318_1, c7_5318_2, c7_5318_3, c7_5318_4, c7_5318_5, c7_5318_6]

end FourColor

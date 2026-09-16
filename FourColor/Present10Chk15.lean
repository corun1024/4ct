import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 15 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_704l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_704l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_704l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_704l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_704l) (hubSubn 10 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_706_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_704l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_706 :
    hubcapFit theRedpart rf10 p10_704l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_706_1, c10_706_2, c10_706_3, c10_706_4, c10_706_5, c10_706_6, c10_706_7, c10_706_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_702l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_702l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_708_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_702l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_708 :
    hubcapFit theRedpart rf10 p10_702l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_708_1, c10_708_2, c10_708_3, c10_708_4, c10_708_5, c10_708_6, c10_708_7, c10_708_8, c10_708_9, c10_708_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_680l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_680l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_680l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_680l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_711_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_680l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_711 :
    hubcapFit theRedpart rf10 p10_680l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_711_1, c10_711_2, c10_711_3, c10_711_4, c10_711_5, c10_711_6, c10_711_7, c10_711_8, c10_711_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_679l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_679l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_679l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_713_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_679l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_713 :
    hubcapFit theRedpart rf10 p10_679l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_713_1, c10_713_2, c10_713_3, c10_713_4, c10_713_5, c10_713_6, c10_713_7, c10_713_8, c10_713_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_677l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_677l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_677l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_677l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_715_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_677l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_715 :
    hubcapFit theRedpart rf10 p10_677l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_715_1, c10_715_2, c10_715_3, c10_715_4, c10_715_5, c10_715_6, c10_715_7, c10_715_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_675l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_675l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_675l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_675l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_675l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_675l) (hubSubn 10 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_717_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_675l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_717 :
    hubcapFit theRedpart rf10 p10_675l
    (Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_717_1, c10_717_2, c10_717_3, c10_717_4, c10_717_5, c10_717_6, c10_717_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_674l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_674l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_674l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_674l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_674l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_674l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_674l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_674l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_719_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_674l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_719 :
    hubcapFit theRedpart rf10 p10_674l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_719_1, c10_719_2, c10_719_3, c10_719_4, c10_719_5, c10_719_6, c10_719_7, c10_719_8, c10_719_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_673l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_673l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_673l) (hubSubn 10 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_721_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_673l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_721 :
    hubcapFit theRedpart rf10 p10_673l
    (Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_721_1, c10_721_2, c10_721_3, c10_721_4, c10_721_5, c10_721_6, c10_721_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_724r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_724r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_724r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_724r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_724r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_724r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_724r) (hubSubn 10 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_725_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_724r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_725 :
    hubcapFit theRedpart rf10 p10_724r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_725_1, c10_725_2, c10_725_3, c10_725_4, c10_725_5, c10_725_6, c10_725_7, c10_725_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_724l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_724l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_724l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_724l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_724l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_724l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_724l) (hubSubn 10 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_726_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_724l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_726 :
    hubcapFit theRedpart rf10 p10_724l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_726_1, c10_726_2, c10_726_3, c10_726_4, c10_726_5, c10_726_6, c10_726_7, c10_726_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_723l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_723l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_723l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_728_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_723l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_728 :
    hubcapFit theRedpart rf10 p10_723l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_728_1, c10_728_2, c10_728_3, c10_728_4, c10_728_5, c10_728_6, c10_728_7, c10_728_8, c10_728_9, c10_728_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_671l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_671l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_671l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_730_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_671l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_730 :
    hubcapFit theRedpart rf10 p10_671l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_730_1, c10_730_2, c10_730_3, c10_730_4, c10_730_5, c10_730_6, c10_730_7, c10_730_8, c10_730_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_670l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_670l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_670l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_670l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_670l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_670l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_670l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_670l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_670l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_732_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_732 :
    hubcapFit theRedpart rf10 p10_670l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_732_1, c10_732_2, c10_732_3, c10_732_4, c10_732_5, c10_732_6, c10_732_7, c10_732_8, c10_732_9, c10_732_10]

end FourColor

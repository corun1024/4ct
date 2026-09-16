import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 57 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2682l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2682l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2682l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2709_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2682l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2709 :
    hubcapFit theRedpart rf9 p9_2682l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2709_1, c9_2709_2, c9_2709_3, c9_2709_4, c9_2709_5, c9_2709_6, c9_2709_7, c9_2709_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2681l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2681l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2681l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2711_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2681l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2711 :
    hubcapFit theRedpart rf9 p9_2681l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2711_1, c9_2711_2, c9_2711_3, c9_2711_4, c9_2711_5, c9_2711_6, c9_2711_7, c9_2711_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2680l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2680l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2713_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2680l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2713 :
    hubcapFit theRedpart rf9 p9_2680l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2713_1, c9_2713_2, c9_2713_3, c9_2713_4, c9_2713_5, c9_2713_6, c9_2713_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2679l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2679l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2715_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2715 :
    hubcapFit theRedpart rf9 p9_2679l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2715_1, c9_2715_2, c9_2715_3, c9_2715_4, c9_2715_5, c9_2715_6, c9_2715_7, c9_2715_8, c9_2715_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2678l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2678l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2717_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2717 :
    hubcapFit theRedpart rf9 p9_2678l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2717_1, c9_2717_2, c9_2717_3, c9_2717_4, c9_2717_5, c9_2717_6, c9_2717_7, c9_2717_8, c9_2717_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2677l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2677l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2677l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2677l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2719_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2719 :
    hubcapFit theRedpart rf9 p9_2677l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2719_1, c9_2719_2, c9_2719_3, c9_2719_4, c9_2719_5, c9_2719_6, c9_2719_7, c9_2719_8, c9_2719_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2676l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2676l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2721_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2721 :
    hubcapFit theRedpart rf9 p9_2676l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2721_1, c9_2721_2, c9_2721_3, c9_2721_4, c9_2721_5, c9_2721_6, c9_2721_7, c9_2721_8, c9_2721_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2750r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2750r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2750r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2750r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2750r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2750r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2751_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2750r) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2751 :
    hubcapFit theRedpart rf9 p9_2750r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2751_1, c9_2751_2, c9_2751_3, c9_2751_4, c9_2751_5, c9_2751_6, c9_2751_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2750l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2750l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2750l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2750l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2750l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2752_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2750l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2752 :
    hubcapFit theRedpart rf9 p9_2750l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2752_1, c9_2752_2, c9_2752_3, c9_2752_4, c9_2752_5, c9_2752_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2749l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2749l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2749l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2749l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2754_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2749l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2754 :
    hubcapFit theRedpart rf9 p9_2749l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2754_1, c9_2754_2, c9_2754_3, c9_2754_4, c9_2754_5, c9_2754_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2747l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2747l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2756_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2747l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2756 :
    hubcapFit theRedpart rf9 p9_2747l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2756_1, c9_2756_2, c9_2756_3, c9_2756_4, c9_2756_5, c9_2756_6, c9_2756_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2765r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2765r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2765r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2766_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2765r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2766 :
    hubcapFit theRedpart rf9 p9_2765r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2766_1, c9_2766_2, c9_2766_3, c9_2766_4, c9_2766_5, c9_2766_6, c9_2766_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2767_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2765l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2767 :
    hubcapFit theRedpart rf9 p9_2765l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2767_1, c9_2767_2, c9_2767_3, c9_2767_4, c9_2767_5, c9_2767_6, c9_2767_7, c9_2767_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2764l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2769_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2764l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2769 :
    hubcapFit theRedpart rf9 p9_2764l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2769_1, c9_2769_2, c9_2769_3, c9_2769_4, c9_2769_5, c9_2769_6, c9_2769_7, c9_2769_8]

end FourColor

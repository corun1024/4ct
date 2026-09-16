import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 107 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5681l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5681l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5681l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5681l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5681l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5689_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5681l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5689 :
    hubcapFit theRedpart rf7 p7_5681l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5689_1, c7_5689_2, c7_5689_3, c7_5689_4, c7_5689_5, c7_5689_6, c7_5689_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5679l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5679l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5691_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5679l) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5691 :
    hubcapFit theRedpart rf7 p7_5679l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5691_1, c7_5691_2, c7_5691_3, c7_5691_4, c7_5691_5, c7_5691_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5678l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5678l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5693_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5678l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5693 :
    hubcapFit theRedpart rf7 p7_5678l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 (-2) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5693_1, c7_5693_2, c7_5693_3, c7_5693_4, c7_5693_5, c7_5693_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5677l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5677l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5694_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5677l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5694 :
    hubcapFit theRedpart rf7 p7_5677l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5694_1, c7_5694_2, c7_5694_3, c7_5694_4, c7_5694_5, c7_5694_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5702r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5702r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5702r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5702r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5702r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5703_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5702r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5703 :
    hubcapFit theRedpart rf7 p7_5702r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5703_1, c7_5703_2, c7_5703_3, c7_5703_4, c7_5703_5, c7_5703_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5702l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5702l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5702l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5704_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5702l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5704 :
    hubcapFit theRedpart rf7 p7_5702l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5704_1, c7_5704_2, c7_5704_3, c7_5704_4, c7_5704_5, c7_5704_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5701l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5701l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5706_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5701l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5706 :
    hubcapFit theRedpart rf7 p7_5701l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5706_1, c7_5706_2, c7_5706_3, c7_5706_4, c7_5706_5, c7_5706_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5707_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5700l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5707_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5700l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5707_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5700l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5707_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5700l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5707_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5700l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5707 :
    hubcapFit theRedpart rf7 p7_5700l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.two 3 6 2 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5707_1, c7_5707_2, c7_5707_3, c7_5707_4, c7_5707_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5699l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5699l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5699l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5699l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5699l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5709_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5699l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5709 :
    hubcapFit theRedpart rf7 p7_5699l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5709_1, c7_5709_2, c7_5709_3, c7_5709_4, c7_5709_5, c7_5709_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5698l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5698l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5698l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5698l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5698l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5710_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5698l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5710 :
    hubcapFit theRedpart rf7 p7_5698l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5710_1, c7_5710_2, c7_5710_3, c7_5710_4, c7_5710_5, c7_5710_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5697l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5697l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5697l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5697l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5697l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5712_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5697l) (hubSubn 7 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5712 :
    hubcapFit theRedpart rf7 p7_5697l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 (-2) <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5712_1, c7_5712_2, c7_5712_3, c7_5712_4, c7_5712_5, c7_5712_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5696l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5696l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5696l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5696l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5713_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5696l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5713 :
    hubcapFit theRedpart rf7 p7_5696l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5713_1, c7_5713_2, c7_5713_3, c7_5713_4, c7_5713_5, c7_5713_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5673l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5673l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5673l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5673l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5715_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5673l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5715 :
    hubcapFit theRedpart rf7 p7_5673l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5715_1, c7_5715_2, c7_5715_3, c7_5715_4, c7_5715_5, c7_5715_6, c7_5715_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5729r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5729r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5729r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5729r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5729r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5729r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5730_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5729r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5730 :
    hubcapFit theRedpart rf7 p7_5729r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5730_1, c7_5730_2, c7_5730_3, c7_5730_4, c7_5730_5, c7_5730_6, c7_5730_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5735r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5735r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5736_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5735r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5736 :
    hubcapFit theRedpart rf7 p7_5735r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-4) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5736_1, c7_5736_2, c7_5736_3, c7_5736_4, c7_5736_5, c7_5736_6, c7_5736_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5735l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5737_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5735l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5737 :
    hubcapFit theRedpart rf7 p7_5735l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5737_1, c7_5737_2, c7_5737_3, c7_5737_4, c7_5737_5, c7_5737_6, c7_5737_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5734l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5734l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5739_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5734l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5739 :
    hubcapFit theRedpart rf7 p7_5734l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5739_1, c7_5739_2, c7_5739_3, c7_5739_4, c7_5739_5, c7_5739_6, c7_5739_7]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 108 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5733l) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5733l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5741_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5733l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5741 :
    hubcapFit theRedpart rf7 p7_5733l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-4) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5741_1, c7_5741_2, c7_5741_3, c7_5741_4, c7_5741_5, c7_5741_6, c7_5741_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5722l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5722l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5722l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5722l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5722l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5743_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5722l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5743 :
    hubcapFit theRedpart rf7 p7_5722l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5743_1, c7_5743_2, c7_5743_3, c7_5743_4, c7_5743_5, c7_5743_6, c7_5743_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5720l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5720l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5720l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5720l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5720l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5720l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5745_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5720l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5745 :
    hubcapFit theRedpart rf7 p7_5720l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5745_1, c7_5745_2, c7_5745_3, c7_5745_4, c7_5745_5, c7_5745_6, c7_5745_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5747r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5747r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5747r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5747r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5747r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5747r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5748_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5747r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5748 :
    hubcapFit theRedpart rf7 p7_5747r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5748_1, c7_5748_2, c7_5748_3, c7_5748_4, c7_5748_5, c7_5748_6, c7_5748_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5747l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5747l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5747l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5749_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5747l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5749 :
    hubcapFit theRedpart rf7 p7_5747l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5749_1, c7_5749_2, c7_5749_3, c7_5749_4, c7_5749_5, c7_5749_6, c7_5749_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5717l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5717l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5717l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5751_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5717l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5751 :
    hubcapFit theRedpart rf7 p7_5717l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5751_1, c7_5751_2, c7_5751_3, c7_5751_4, c7_5751_5, c7_5751_6, c7_5751_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5671l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5671l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5753_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5671l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5753 :
    hubcapFit theRedpart rf7 p7_5671l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5753_1, c7_5753_2, c7_5753_3, c7_5753_4, c7_5753_5, c7_5753_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5764r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5764r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5764r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5764r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5764r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5764r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5765_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5764r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5765 :
    hubcapFit theRedpart rf7 p7_5764r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5765_1, c7_5765_2, c7_5765_3, c7_5765_4, c7_5765_5, c7_5765_6, c7_5765_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5764l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5764l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5766_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5766 :
    hubcapFit theRedpart rf7 p7_5764l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5766_1, c7_5766_2, c7_5766_3, c7_5766_4, c7_5766_5, c7_5766_6, c7_5766_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5763l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5763l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5768_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5763l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5768 :
    hubcapFit theRedpart rf7 p7_5763l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5768_1, c7_5768_2, c7_5768_3, c7_5768_4, c7_5768_5, c7_5768_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5760l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5760l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5760l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5760l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5760l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5760l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5770_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5760l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5770 :
    hubcapFit theRedpart rf7 p7_5760l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5770_1, c7_5770_2, c7_5770_3, c7_5770_4, c7_5770_5, c7_5770_6, c7_5770_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5759l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5759l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5759l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5759l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5759l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5772_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5759l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5772 :
    hubcapFit theRedpart rf7 p7_5759l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5772_1, c7_5772_2, c7_5772_3, c7_5772_4, c7_5772_5, c7_5772_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5777r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5777r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5777r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5778_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5777r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5778 :
    hubcapFit theRedpart rf7 p7_5777r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5778_1, c7_5778_2, c7_5778_3, c7_5778_4, c7_5778_5, c7_5778_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5777l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5777l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5777l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5777l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5777l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5779_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5777l) (hubSubn 7 5 4) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5779 :
    hubcapFit theRedpart rf7 p7_5777l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5779_1, c7_5779_2, c7_5779_3, c7_5779_4, c7_5779_5, c7_5779_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5774l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5774l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5774l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5774l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5774l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5781_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5774l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5781 :
    hubcapFit theRedpart rf7 p7_5774l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5781_1, c7_5781_2, c7_5781_3, c7_5781_4, c7_5781_5, c7_5781_6, c7_5781_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5773l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5773l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5773l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5783_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5773l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5783 :
    hubcapFit theRedpart rf7 p7_5773l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5783_1, c7_5783_2, c7_5783_3, c7_5783_4, c7_5783_5, c7_5783_6]

end FourColor

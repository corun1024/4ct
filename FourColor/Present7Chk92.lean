import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 92 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4879l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4879l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4879l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4879l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4879l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4879l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4890_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4879l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4890 :
    hubcapFit theRedpart rf7 p7_4879l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4890_1, c7_4890_2, c7_4890_3, c7_4890_4, c7_4890_5, c7_4890_6, c7_4890_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4878l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4878l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4878l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4892_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4878l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4892 :
    hubcapFit theRedpart rf7 p7_4878l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4892_1, c7_4892_2, c7_4892_3, c7_4892_4, c7_4892_5, c7_4892_6, c7_4892_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4900r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4900r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4900r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4900r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4900r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4900r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4901_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4900r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4901 :
    hubcapFit theRedpart rf7 p7_4900r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4901_1, c7_4901_2, c7_4901_3, c7_4901_4, c7_4901_5, c7_4901_6, c7_4901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4900l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4900l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4900l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4900l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4900l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4900l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4902_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4900l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4902 :
    hubcapFit theRedpart rf7 p7_4900l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4902_1, c7_4902_2, c7_4902_3, c7_4902_4, c7_4902_5, c7_4902_6, c7_4902_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4899l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4899l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4899l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4899l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4904_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4899l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4904 :
    hubcapFit theRedpart rf7 p7_4899l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4904_1, c7_4904_2, c7_4904_3, c7_4904_4, c7_4904_5, c7_4904_6, c7_4904_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4897l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4897l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4897l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4897l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4906_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4897l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4906 :
    hubcapFit theRedpart rf7 p7_4897l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4906_1, c7_4906_2, c7_4906_3, c7_4906_4, c7_4906_5, c7_4906_6, c7_4906_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4896l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4896l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4896l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4896l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4896l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4896l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4908_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4896l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4908 :
    hubcapFit theRedpart rf7 p7_4896l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4908_1, c7_4908_2, c7_4908_3, c7_4908_4, c7_4908_5, c7_4908_6, c7_4908_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4912r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4912r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4912r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4912r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4912r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4912r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4913_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4912r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4913 :
    hubcapFit theRedpart rf7 p7_4912r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4913_1, c7_4913_2, c7_4913_3, c7_4913_4, c7_4913_5, c7_4913_6, c7_4913_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4912l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4914_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4912l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4914 :
    hubcapFit theRedpart rf7 p7_4912l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4914_1, c7_4914_2, c7_4914_3, c7_4914_4, c7_4914_5, c7_4914_6, c7_4914_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4911l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4911l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4911l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4911l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4916_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4911l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4916 :
    hubcapFit theRedpart rf7 p7_4911l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4916_1, c7_4916_2, c7_4916_3, c7_4916_4, c7_4916_5, c7_4916_6, c7_4916_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4910l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4910l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4910l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4910l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4910l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4918_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4910l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4918 :
    hubcapFit theRedpart rf7 p7_4910l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4918_1, c7_4918_2, c7_4918_3, c7_4918_4, c7_4918_5, c7_4918_6, c7_4918_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4925r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4925r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4925r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4925r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4925r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4925r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4926_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4925r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4926 :
    hubcapFit theRedpart rf7 p7_4925r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4926_1, c7_4926_2, c7_4926_3, c7_4926_4, c7_4926_5, c7_4926_6, c7_4926_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4925l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4925l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4925l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4927_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4925l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4927 :
    hubcapFit theRedpart rf7 p7_4925l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4927_1, c7_4927_2, c7_4927_3, c7_4927_4, c7_4927_5, c7_4927_6, c7_4927_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4924l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4924l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4924l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4924l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4929_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4924l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4929 :
    hubcapFit theRedpart rf7 p7_4924l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4929_1, c7_4929_2, c7_4929_3, c7_4929_4, c7_4929_5, c7_4929_6, c7_4929_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4922l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4922l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4922l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4922l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4922l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4922l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4931_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4922l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4931 :
    hubcapFit theRedpart rf7 p7_4922l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4931_1, c7_4931_2, c7_4931_3, c7_4931_4, c7_4931_5, c7_4931_6, c7_4931_7]

end FourColor

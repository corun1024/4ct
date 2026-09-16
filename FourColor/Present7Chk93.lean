import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 93 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4921l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4921l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4921l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4921l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4921l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4921l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4933_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4921l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4933 :
    hubcapFit theRedpart rf7 p7_4921l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4933_1, c7_4933_2, c7_4933_3, c7_4933_4, c7_4933_5, c7_4933_6, c7_4933_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4937r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4937r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4937r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4937r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4937r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4937r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4938_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4937r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4938 :
    hubcapFit theRedpart rf7 p7_4937r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4938_1, c7_4938_2, c7_4938_3, c7_4938_4, c7_4938_5, c7_4938_6, c7_4938_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4937l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4937l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4937l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4939_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4937l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4939 :
    hubcapFit theRedpart rf7 p7_4937l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4939_1, c7_4939_2, c7_4939_3, c7_4939_4, c7_4939_5, c7_4939_6, c7_4939_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4936l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4936l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4936l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4941_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4936l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4941 :
    hubcapFit theRedpart rf7 p7_4936l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4941_1, c7_4941_2, c7_4941_3, c7_4941_4, c7_4941_5, c7_4941_6, c7_4941_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4935l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4935l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4935l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4935l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4943_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4935l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4943 :
    hubcapFit theRedpart rf7 p7_4935l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4943_1, c7_4943_2, c7_4943_3, c7_4943_4, c7_4943_5, c7_4943_6, c7_4943_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4952r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4952r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4952r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4952r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4952r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4952r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4953_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4952r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4953 :
    hubcapFit theRedpart rf7 p7_4952r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4953_1, c7_4953_2, c7_4953_3, c7_4953_4, c7_4953_5, c7_4953_6, c7_4953_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4952l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4952l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4952l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4952l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4952l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4952l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4954_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4952l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4954 :
    hubcapFit theRedpart rf7 p7_4952l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4954_1, c7_4954_2, c7_4954_3, c7_4954_4, c7_4954_5, c7_4954_6, c7_4954_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4950l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4950l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4950l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4950l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4950l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4956_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4950l) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4956 :
    hubcapFit theRedpart rf7 p7_4950l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4956_1, c7_4956_2, c7_4956_3, c7_4956_4, c7_4956_5, c7_4956_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4949l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4949l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4949l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4949l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4958_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4949l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4958 :
    hubcapFit theRedpart rf7 p7_4949l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4958_1, c7_4958_2, c7_4958_3, c7_4958_4, c7_4958_5, c7_4958_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4946l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4946l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4946l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4946l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4946l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4960_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4946l) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4960 :
    hubcapFit theRedpart rf7 p7_4946l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4960_1, c7_4960_2, c7_4960_3, c7_4960_4, c7_4960_5, c7_4960_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4965r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4965r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4965r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4965r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4965r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4965r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4966_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4965r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4966 :
    hubcapFit theRedpart rf7 p7_4965r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4966_1, c7_4966_2, c7_4966_3, c7_4966_4, c7_4966_5, c7_4966_6, c7_4966_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4965l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4965l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4967_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4967 :
    hubcapFit theRedpart rf7 p7_4965l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4967_1, c7_4967_2, c7_4967_3, c7_4967_4, c7_4967_5, c7_4967_6, c7_4967_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4963l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4963l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4963l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4969_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4963l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4969 :
    hubcapFit theRedpart rf7 p7_4963l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4969_1, c7_4969_2, c7_4969_3, c7_4969_4, c7_4969_5, c7_4969_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4962l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4962l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4971_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4962l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4971 :
    hubcapFit theRedpart rf7 p7_4962l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4971_1, c7_4971_2, c7_4971_3, c7_4971_4, c7_4971_5, c7_4971_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5000r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5000r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5000r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5000r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5001_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5000r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5001 :
    hubcapFit theRedpart rf7 p7_5000r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5001_1, c7_5001_2, c7_5001_3, c7_5001_4, c7_5001_5, c7_5001_6, c7_5001_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5002_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5002_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5002_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5000l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5002_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5000l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5002_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5000l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5002 :
    hubcapFit theRedpart rf7 p7_5000l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5002_1, c7_5002_2, c7_5002_3, c7_5002_4, c7_5002_5]

end FourColor

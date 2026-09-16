import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 17 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_942_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_921l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_942_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_921l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_942_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_921l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_942_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_921l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_942_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_921l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_942 :
    hubcapFit theRedpart rf7 p7_921l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_942_1, c7_942_2, c7_942_3, c7_942_4, c7_942_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_944_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_920l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_944_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_920l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_944_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_920l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_944_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_920l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_944 :
    hubcapFit theRedpart rf7 p7_920l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_944_1, c7_944_2, c7_944_3, c7_944_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_945_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_919l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_945 :
    hubcapFit theRedpart rf7 p7_919l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_945_1, c7_945_2, c7_945_3, c7_945_4, c7_945_5, c7_945_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_947_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_947_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_947_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_918l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_947_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_918l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_947_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_918l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_947 :
    hubcapFit theRedpart rf7 p7_918l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_947_1, c7_947_2, c7_947_3, c7_947_4, c7_947_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_949_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_910l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_949_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_949_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_910l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_949_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_910l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_949_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_910l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_949 :
    hubcapFit theRedpart rf7 p7_910l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_949_1, c7_949_2, c7_949_3, c7_949_4, c7_949_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_950_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_909l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_950_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_909l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_950_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_909l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_950_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_909l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_950_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_909l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_950 :
    hubcapFit theRedpart rf7 p7_909l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_950_1, c7_950_2, c7_950_3, c7_950_4, c7_950_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_892l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_892l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_952_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_892l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_952 :
    hubcapFit theRedpart rf7 p7_892l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_952_1, c7_952_2, c7_952_3, c7_952_4, c7_952_5, c7_952_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_891l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_891l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_891l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_891l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_954_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_891l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_954 :
    hubcapFit theRedpart rf7 p7_891l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_954_1, c7_954_2, c7_954_3, c7_954_4, c7_954_5, c7_954_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_966_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_965r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_966_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_965r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_966_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_965r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_966_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_965r) (hubSubn 7 3 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_966_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_965r) (hubSubn 7 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_966 :
    hubcapFit theRedpart rf7 p7_965r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_966_1, c7_966_2, c7_966_3, c7_966_4, c7_966_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_980r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_980r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_980r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_980r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_980r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_980r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_981_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_980r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_981 :
    hubcapFit theRedpart rf7 p7_980r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_981_1, c7_981_2, c7_981_3, c7_981_4, c7_981_5, c7_981_6, c7_981_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_980l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_980l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_980l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_982_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_980l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_982 :
    hubcapFit theRedpart rf7 p7_980l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_982_1, c7_982_2, c7_982_3, c7_982_4, c7_982_5, c7_982_6, c7_982_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_979l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_979l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_984_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_979l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_984 :
    hubcapFit theRedpart rf7 p7_979l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_984_1, c7_984_2, c7_984_3, c7_984_4, c7_984_5, c7_984_6, c7_984_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_976l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_976l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_976l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_976l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_976l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_976l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_986_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_976l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_986 :
    hubcapFit theRedpart rf7 p7_976l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_986_1, c7_986_2, c7_986_3, c7_986_4, c7_986_5, c7_986_6, c7_986_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_988_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_988 :
    hubcapFit theRedpart rf7 p7_975l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_988_1, c7_988_2, c7_988_3, c7_988_4, c7_988_5, c7_988_6, c7_988_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_971l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_971l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_990_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_971l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_990 :
    hubcapFit theRedpart rf7 p7_971l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_990_1, c7_990_2, c7_990_3, c7_990_4, c7_990_5, c7_990_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_970l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_970l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_992_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_970l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_992 :
    hubcapFit theRedpart rf7 p7_970l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_992_1, c7_992_2, c7_992_3, c7_992_4, c7_992_5, c7_992_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_993_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_993 :
    hubcapFit theRedpart rf7 p7_969l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_993_1, c7_993_2, c7_993_3, c7_993_4, c7_993_5, c7_993_6, c7_993_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_968l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_968l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_995_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_968l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_995 :
    hubcapFit theRedpart rf7 p7_968l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_995_1, c7_995_2, c7_995_3, c7_995_4, c7_995_5, c7_995_6]

end FourColor

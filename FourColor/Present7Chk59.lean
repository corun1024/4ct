import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 59 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3183l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3183l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3183l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3188_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3188 :
    hubcapFit theRedpart rf7 p7_3183l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3188_1, c7_3188_2, c7_3188_3, c7_3188_4, c7_3188_5, c7_3188_6, c7_3188_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3182l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3182l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3182l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3190_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3190 :
    hubcapFit theRedpart rf7 p7_3182l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3190_1, c7_3190_2, c7_3190_3, c7_3190_4, c7_3190_5, c7_3190_6, c7_3190_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3181l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3181l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3192_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3181l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3192 :
    hubcapFit theRedpart rf7 p7_3181l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3192_1, c7_3192_2, c7_3192_3, c7_3192_4, c7_3192_5, c7_3192_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3195r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3195r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3195r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3196_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3195r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3196 :
    hubcapFit theRedpart rf7 p7_3195r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3196_1, c7_3196_2, c7_3196_3, c7_3196_4, c7_3196_5, c7_3196_6, c7_3196_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3206r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3206r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3206r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3206r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3206r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3206r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3207_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3206r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3207 :
    hubcapFit theRedpart rf7 p7_3206r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3207_1, c7_3207_2, c7_3207_3, c7_3207_4, c7_3207_5, c7_3207_6, c7_3207_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3206l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3206l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3208_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3208 :
    hubcapFit theRedpart rf7 p7_3206l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3208_1, c7_3208_2, c7_3208_3, c7_3208_4, c7_3208_5, c7_3208_6, c7_3208_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3205l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3205l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3205l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3210_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3205l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3210 :
    hubcapFit theRedpart rf7 p7_3205l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3210_1, c7_3210_2, c7_3210_3, c7_3210_4, c7_3210_5, c7_3210_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3217r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3217r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3217r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3218_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3217r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3218 :
    hubcapFit theRedpart rf7 p7_3217r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3218_1, c7_3218_2, c7_3218_3, c7_3218_4, c7_3218_5, c7_3218_6, c7_3218_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3217l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3217l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3217l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3217l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3219_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3219 :
    hubcapFit theRedpart rf7 p7_3217l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3219_1, c7_3219_2, c7_3219_3, c7_3219_4, c7_3219_5, c7_3219_6, c7_3219_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3214l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3214l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3221_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3221 :
    hubcapFit theRedpart rf7 p7_3214l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3221_1, c7_3221_2, c7_3221_3, c7_3221_4, c7_3221_5, c7_3221_6, c7_3221_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3223_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3212l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3223_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3223_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3212l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3223_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3212l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3223_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3212l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3223 :
    hubcapFit theRedpart rf7 p7_3212l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3223_1, c7_3223_2, c7_3223_3, c7_3223_4, c7_3223_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3226r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3226r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3226r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3226r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3226r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3226r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3227_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3226r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3227 :
    hubcapFit theRedpart rf7 p7_3226r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3227_1, c7_3227_2, c7_3227_3, c7_3227_4, c7_3227_5, c7_3227_6, c7_3227_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3226l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3226l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3228_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3226l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3228 :
    hubcapFit theRedpart rf7 p7_3226l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3228_1, c7_3228_2, c7_3228_3, c7_3228_4, c7_3228_5, c7_3228_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3231_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3231_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3200l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3231_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3200l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3231_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3200l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3231_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3200l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3231 :
    hubcapFit theRedpart rf7 p7_3200l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3231_1, c7_3231_2, c7_3231_3, c7_3231_4, c7_3231_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3238r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3238r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3238r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3238r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3239_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3239 :
    hubcapFit theRedpart rf7 p7_3238r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3239_1, c7_3239_2, c7_3239_3, c7_3239_4, c7_3239_5, c7_3239_6, c7_3239_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3238l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3238l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3238l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3238l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3238l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3240_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3240 :
    hubcapFit theRedpart rf7 p7_3238l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3240_1, c7_3240_2, c7_3240_3, c7_3240_4, c7_3240_5, c7_3240_6, c7_3240_7]

end FourColor

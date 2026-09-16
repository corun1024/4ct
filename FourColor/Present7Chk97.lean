import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 97 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5150l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5150l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5150l) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5152_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5150l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5152 :
    hubcapFit theRedpart rf7 p7_5150l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5152_1, c7_5152_2, c7_5152_3, c7_5152_4, c7_5152_5, c7_5152_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5154_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5154_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5154_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5149l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5154_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5149l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5154_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5149l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5154 :
    hubcapFit theRedpart rf7 p7_5149l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5154_1, c7_5154_2, c7_5154_3, c7_5154_4, c7_5154_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5148l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5148l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5148l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5155_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5148l) (hubSubn 7 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5155 :
    hubcapFit theRedpart rf7 p7_5148l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5155_1, c7_5155_2, c7_5155_3, c7_5155_4, c7_5155_5, c7_5155_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5157_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5125l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5157_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5125l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5157_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5125l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5157_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5125l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5157_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5125l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5157 :
    hubcapFit theRedpart rf7 p7_5125l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5157_1, c7_5157_2, c7_5157_3, c7_5157_4, c7_5157_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5162r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5162r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5162r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5162r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5162r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5163_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5162r) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5163 :
    hubcapFit theRedpart rf7 p7_5162r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5163_1, c7_5163_2, c7_5163_3, c7_5163_4, c7_5163_5, c7_5163_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5162l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5162l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5162l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5162l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5162l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5164_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5162l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5164 :
    hubcapFit theRedpart rf7 p7_5162l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5164_1, c7_5164_2, c7_5164_3, c7_5164_4, c7_5164_5, c7_5164_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5161l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5161l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5166_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5161l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5166 :
    hubcapFit theRedpart rf7 p7_5161l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5166_1, c7_5166_2, c7_5166_3, c7_5166_4, c7_5166_5, c7_5166_6, c7_5166_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5168_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5168_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5168_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5160l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5168_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5160l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5168_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5160l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5168 :
    hubcapFit theRedpart rf7 p7_5160l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5168_1, c7_5168_2, c7_5168_3, c7_5168_4, c7_5168_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5175r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5175r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5175r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5175r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5175r) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5176_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5175r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5176 :
    hubcapFit theRedpart rf7 p7_5175r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5176_1, c7_5176_2, c7_5176_3, c7_5176_4, c7_5176_5, c7_5176_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5177_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5177_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5177_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5177_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5175l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5177_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5175l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5177 :
    hubcapFit theRedpart rf7 p7_5175l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5177_1, c7_5177_2, c7_5177_3, c7_5177_4, c7_5177_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5179_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5179_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5179_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5174l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5179_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5174l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5179_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5174l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5179 :
    hubcapFit theRedpart rf7 p7_5174l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5179_1, c7_5179_2, c7_5179_3, c7_5179_4, c7_5179_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5172l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5172l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5172l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5181_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5172l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5181 :
    hubcapFit theRedpart rf7 p7_5172l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5181_1, c7_5181_2, c7_5181_3, c7_5181_4, c7_5181_5, c7_5181_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5171l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5171l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5171l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5171l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5182_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5171l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5182 :
    hubcapFit theRedpart rf7 p7_5171l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5182_1, c7_5182_2, c7_5182_3, c7_5182_4, c7_5182_5, c7_5182_6, c7_5182_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5191r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5191r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5191r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5191r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5191r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5191r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5192_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5191r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5192 :
    hubcapFit theRedpart rf7 p7_5191r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5192_1, c7_5192_2, c7_5192_3, c7_5192_4, c7_5192_5, c7_5192_6, c7_5192_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5193_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5191l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5193_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5191l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5193_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5191l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5193_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5191l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5193_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5191l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5193 :
    hubcapFit theRedpart rf7 p7_5191l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5193_1, c7_5193_2, c7_5193_3, c7_5193_4, c7_5193_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5195_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5195_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5195_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5189l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5195_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5189l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5195_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5189l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5195 :
    hubcapFit theRedpart rf7 p7_5189l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5195_1, c7_5195_2, c7_5195_3, c7_5195_4, c7_5195_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5188l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5188l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5197_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5188l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5197 :
    hubcapFit theRedpart rf7 p7_5188l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5197_1, c7_5197_2, c7_5197_3, c7_5197_4, c7_5197_5, c7_5197_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5198_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5198_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5198_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5187l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5198_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5187l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5198_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5187l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5198 :
    hubcapFit theRedpart rf7 p7_5187l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5198_1, c7_5198_2, c7_5198_3, c7_5198_4, c7_5198_5]

end FourColor

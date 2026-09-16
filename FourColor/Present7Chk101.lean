import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 101 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5384r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5384r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5384r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5384r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5384r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5385_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5384r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5385 :
    hubcapFit theRedpart rf7 p7_5384r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5385_1, c7_5385_2, c7_5385_3, c7_5385_4, c7_5385_5, c7_5385_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5384l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5384l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5384l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5384l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5384l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5386_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5384l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5386 :
    hubcapFit theRedpart rf7 p7_5384l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5386_1, c7_5386_2, c7_5386_3, c7_5386_4, c7_5386_5, c7_5386_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5383l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5383l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5383l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5388_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5383l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5388 :
    hubcapFit theRedpart rf7 p7_5383l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5388_1, c7_5388_2, c7_5388_3, c7_5388_4, c7_5388_5, c7_5388_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5382l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5382l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5382l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5382l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5382l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5389_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5382l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5389 :
    hubcapFit theRedpart rf7 p7_5382l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5389_1, c7_5389_2, c7_5389_3, c7_5389_4, c7_5389_5, c7_5389_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5381l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5381l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5381l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5381l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5381l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5391_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5381l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5391 :
    hubcapFit theRedpart rf7 p7_5381l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5391_1, c7_5391_2, c7_5391_3, c7_5391_4, c7_5391_5, c7_5391_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5378l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5393_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5378l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5393 :
    hubcapFit theRedpart rf7 p7_5378l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5393_1, c7_5393_2, c7_5393_3, c7_5393_4, c7_5393_5, c7_5393_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5396r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5396r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5396r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5396r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5396r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5397_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5396r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5397 :
    hubcapFit theRedpart rf7 p7_5396r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5397_1, c7_5397_2, c7_5397_3, c7_5397_4, c7_5397_5, c7_5397_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5396l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5396l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5396l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5396l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5396l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5398_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5396l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5398 :
    hubcapFit theRedpart rf7 p7_5396l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5398_1, c7_5398_2, c7_5398_3, c7_5398_4, c7_5398_5, c7_5398_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5395l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5395l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5395l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5395l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5400_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5395l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5400 :
    hubcapFit theRedpart rf7 p7_5395l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5400_1, c7_5400_2, c7_5400_3, c7_5400_4, c7_5400_5, c7_5400_6, c7_5400_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5418r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5418r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5418r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5418r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5419_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5418r) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5419 :
    hubcapFit theRedpart rf7 p7_5418r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5419_1, c7_5419_2, c7_5419_3, c7_5419_4, c7_5419_5, c7_5419_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5423r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5423r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5423r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5423r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5423r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5424_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5423r) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5424 :
    hubcapFit theRedpart rf7 p7_5423r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5424_1, c7_5424_2, c7_5424_3, c7_5424_4, c7_5424_5, c7_5424_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5423l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5423l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5423l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5425_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5423l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5425 :
    hubcapFit theRedpart rf7 p7_5423l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5425_1, c7_5425_2, c7_5425_3, c7_5425_4, c7_5425_5, c7_5425_6, c7_5425_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5422l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5422l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5427_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5422l) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5427 :
    hubcapFit theRedpart rf7 p7_5422l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5427_1, c7_5427_2, c7_5427_3, c7_5427_4, c7_5427_5, c7_5427_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5421l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5421l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5421l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5421l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5421l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5428_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5421l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5428 :
    hubcapFit theRedpart rf7 p7_5421l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5428_1, c7_5428_2, c7_5428_3, c7_5428_4, c7_5428_5, c7_5428_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5433r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5433r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5433r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5433r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5433r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5434_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5433r) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5434 :
    hubcapFit theRedpart rf7 p7_5433r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5434_1, c7_5434_2, c7_5434_3, c7_5434_4, c7_5434_5, c7_5434_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5433l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5433l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5433l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5433l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5433l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5433l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5435_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5433l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5435 :
    hubcapFit theRedpart rf7 p7_5433l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5435_1, c7_5435_2, c7_5435_3, c7_5435_4, c7_5435_5, c7_5435_6, c7_5435_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5432l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5432l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5432l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5437_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5432l) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5437 :
    hubcapFit theRedpart rf7 p7_5432l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5437_1, c7_5437_2, c7_5437_3, c7_5437_4, c7_5437_5, c7_5437_6]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 102 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5431l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5431l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5431l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5431l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5431l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5438_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5431l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5438 :
    hubcapFit theRedpart rf7 p7_5431l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5438_1, c7_5438_2, c7_5438_3, c7_5438_4, c7_5438_5, c7_5438_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5430l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5430l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5430l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5430l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5430l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5430l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5440_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5430l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5440 :
    hubcapFit theRedpart rf7 p7_5430l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5440_1, c7_5440_2, c7_5440_3, c7_5440_4, c7_5440_5, c7_5440_6, c7_5440_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5444r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5444r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5444r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5444r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5444r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5445_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5444r) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5445 :
    hubcapFit theRedpart rf7 p7_5444r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5445_1, c7_5445_2, c7_5445_3, c7_5445_4, c7_5445_5, c7_5445_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5444l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5444l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5446_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5444l) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5446 :
    hubcapFit theRedpart rf7 p7_5444l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5446_1, c7_5446_2, c7_5446_3, c7_5446_4, c7_5446_5, c7_5446_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5443l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5448_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5443l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5448 :
    hubcapFit theRedpart rf7 p7_5443l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5448_1, c7_5448_2, c7_5448_3, c7_5448_4, c7_5448_5, c7_5448_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5442l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5442l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5449_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5442l) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5449 :
    hubcapFit theRedpart rf7 p7_5442l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5449_1, c7_5449_2, c7_5449_3, c7_5449_4, c7_5449_5, c7_5449_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5457r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5457r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5457r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5457r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5457r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5458_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5457r) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5458 :
    hubcapFit theRedpart rf7 p7_5457r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5458_1, c7_5458_2, c7_5458_3, c7_5458_4, c7_5458_5, c7_5458_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5457l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5457l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5457l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5459_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5457l) (hubSubn 7 5 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5459 :
    hubcapFit theRedpart rf7 p7_5457l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5459_1, c7_5459_2, c7_5459_3, c7_5459_4, c7_5459_5, c7_5459_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5456l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5461_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5456l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5461 :
    hubcapFit theRedpart rf7 p7_5456l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5461_1, c7_5461_2, c7_5461_3, c7_5461_4, c7_5461_5, c7_5461_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5455l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5455l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5455l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5455l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5455l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5462_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5455l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5462 :
    hubcapFit theRedpart rf7 p7_5455l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5462_1, c7_5462_2, c7_5462_3, c7_5462_4, c7_5462_5, c7_5462_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5454l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5454l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5454l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5454l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5454l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5464_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5454l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5464 :
    hubcapFit theRedpart rf7 p7_5454l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5464_1, c7_5464_2, c7_5464_3, c7_5464_4, c7_5464_5, c7_5464_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5453l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5453l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5465_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5453l) (hubSubn 7 5 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5465 :
    hubcapFit theRedpart rf7 p7_5453l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5465_1, c7_5465_2, c7_5465_3, c7_5465_4, c7_5465_5, c7_5465_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5452l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5467_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5452l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5467 :
    hubcapFit theRedpart rf7 p7_5452l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5467_1, c7_5467_2, c7_5467_3, c7_5467_4, c7_5467_5, c7_5467_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5474r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5474r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5474r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5474r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5474r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5475_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5474r) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5475 :
    hubcapFit theRedpart rf7 p7_5474r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5475_1, c7_5475_2, c7_5475_3, c7_5475_4, c7_5475_5, c7_5475_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5474l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5474l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5474l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5476_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5474l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5476 :
    hubcapFit theRedpart rf7 p7_5474l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5476_1, c7_5476_2, c7_5476_3, c7_5476_4, c7_5476_5, c7_5476_6, c7_5476_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5473l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5473l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5473l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5478_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5473l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5478 :
    hubcapFit theRedpart rf7 p7_5473l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5478_1, c7_5478_2, c7_5478_3, c7_5478_4, c7_5478_5, c7_5478_6, c7_5478_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5472l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5480_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5472l) (hubSubn 7 6 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5480 :
    hubcapFit theRedpart rf7 p7_5472l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5480_1, c7_5480_2, c7_5480_3, c7_5480_4, c7_5480_5, c7_5480_6]

end FourColor

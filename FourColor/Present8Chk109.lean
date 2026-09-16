import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 109 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5424l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5434_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5424l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5434 :
    hubcapFit theRedpart rf8 p8_5424l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5434_1, c8_5434_2, c8_5434_3, c8_5434_4, c8_5434_5, c8_5434_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5423l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5423l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5423l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5423l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5435_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5423l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5435 :
    hubcapFit theRedpart rf8 p8_5423l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5435_1, c8_5435_2, c8_5435_3, c8_5435_4, c8_5435_5, c8_5435_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5323l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5438_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5323l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5438 :
    hubcapFit theRedpart rf8 p8_5323l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5438_1, c8_5438_2, c8_5438_3, c8_5438_4, c8_5438_5, c8_5438_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5446r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5446r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5446r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5446r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5446r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5446r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5446r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5447_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5446r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5447 :
    hubcapFit theRedpart rf8 p8_5446r
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5447_1, c8_5447_2, c8_5447_3, c8_5447_4, c8_5447_5, c8_5447_6, c8_5447_7, c8_5447_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5444l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5449_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5449 :
    hubcapFit theRedpart rf8 p8_5444l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5449_1, c8_5449_2, c8_5449_3, c8_5449_4, c8_5449_5, c8_5449_6, c8_5449_7, c8_5449_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5443l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5443l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5451_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5443l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5451 :
    hubcapFit theRedpart rf8 p8_5443l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5451_1, c8_5451_2, c8_5451_3, c8_5451_4, c8_5451_5, c8_5451_6, c8_5451_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5442l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5442l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5453_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5442l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5453 :
    hubcapFit theRedpart rf8 p8_5442l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5453_1, c8_5453_2, c8_5453_3, c8_5453_4, c8_5453_5, c8_5453_6, c8_5453_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5464r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5464r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5464r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5464r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5464r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5464r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5465_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5464r) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5465 :
    hubcapFit theRedpart rf8 p8_5464r
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5465_1, c8_5465_2, c8_5465_3, c8_5465_4, c8_5465_5, c8_5465_6, c8_5465_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5464l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5464l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5464l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5464l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5464l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5466_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5464l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5466 :
    hubcapFit theRedpart rf8 p8_5464l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5466_1, c8_5466_2, c8_5466_3, c8_5466_4, c8_5466_5, c8_5466_6, c8_5466_7, c8_5466_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5463l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5463l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5463l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5463l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5463l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5463l) (hubSubn 8 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5468_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5463l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5468 :
    hubcapFit theRedpart rf8 p8_5463l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5468_1, c8_5468_2, c8_5468_3, c8_5468_4, c8_5468_5, c8_5468_6, c8_5468_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5473r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5473r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5473r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5473r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5473r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5473r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5474_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5473r) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5474 :
    hubcapFit theRedpart rf8 p8_5473r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5474_1, c8_5474_2, c8_5474_3, c8_5474_4, c8_5474_5, c8_5474_6, c8_5474_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5475_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5475_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5473l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5475_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5473l) (hubSubn 8 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5475_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5473l) (hubSubn 8 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5475_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5473l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5475 :
    hubcapFit theRedpart rf8 p8_5473l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5475_1, c8_5475_2, c8_5475_3, c8_5475_4, c8_5475_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5472l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5472l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5472l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5472l) (hubSubn 8 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5477_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5472l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5477 :
    hubcapFit theRedpart rf8 p8_5472l
    (Hubcap.one 0 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5477_1, c8_5477_2, c8_5477_3, c8_5477_4, c8_5477_5, c8_5477_6, c8_5477_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5481r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5481r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5481r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5481r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5481r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5481r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5482_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5481r) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5482 :
    hubcapFit theRedpart rf8 p8_5481r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5482_1, c8_5482_2, c8_5482_3, c8_5482_4, c8_5482_5, c8_5482_6, c8_5482_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5481l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5481l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5481l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5481l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5481l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5483_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5481l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5483 :
    hubcapFit theRedpart rf8 p8_5481l
    (Hubcap.one 0 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5483_1, c8_5483_2, c8_5483_3, c8_5483_4, c8_5483_5, c8_5483_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5480l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5480l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5480l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5480l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5480l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5480l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5485_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5480l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5485 :
    hubcapFit theRedpart rf8 p8_5480l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5485_1, c8_5485_2, c8_5485_3, c8_5485_4, c8_5485_5, c8_5485_6, c8_5485_7]

end FourColor

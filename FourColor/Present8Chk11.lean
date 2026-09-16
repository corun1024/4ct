import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 11 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_531l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_531l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_531l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_543_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_531l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_543 :
    hubcapFit theRedpart rf8 p8_531l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_543_1, c8_543_2, c8_543_3, c8_543_4, c8_543_5, c8_543_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_530l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_545_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_530l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_545 :
    hubcapFit theRedpart rf8 p8_530l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_545_1, c8_545_2, c8_545_3, c8_545_4, c8_545_5, c8_545_6, c8_545_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_529l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_529l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_529l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_529l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_529l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_547_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_529l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_547 :
    hubcapFit theRedpart rf8 p8_529l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_547_1, c8_547_2, c8_547_3, c8_547_4, c8_547_5, c8_547_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_548_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_528l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_548 :
    hubcapFit theRedpart rf8 p8_528l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_548_1, c8_548_2, c8_548_3, c8_548_4, c8_548_5, c8_548_6, c8_548_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_527l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_550_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_527l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_550 :
    hubcapFit theRedpart rf8 p8_527l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_550_1, c8_550_2, c8_550_3, c8_550_4, c8_550_5, c8_550_6, c8_550_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_526l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_552_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_526l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_552 :
    hubcapFit theRedpart rf8 p8_526l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_552_1, c8_552_2, c8_552_3, c8_552_4, c8_552_5, c8_552_6, c8_552_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_554_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_445l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_554 :
    hubcapFit theRedpart rf8 p8_445l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_554_1, c8_554_2, c8_554_3, c8_554_4, c8_554_5, c8_554_6, c8_554_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_444l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_444l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_556_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_444l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_556 :
    hubcapFit theRedpart rf8 p8_444l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_556_1, c8_556_2, c8_556_3, c8_556_4, c8_556_5, c8_556_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_443l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_557_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_443l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_557 :
    hubcapFit theRedpart rf8 p8_443l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_557_1, c8_557_2, c8_557_3, c8_557_4, c8_557_5, c8_557_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_559_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_126l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_559_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_126l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_559_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_126l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_559_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_126l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_559_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_126l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_559 :
    hubcapFit theRedpart rf8 p8_126l
    (Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_559_1, c8_559_2, c8_559_3, c8_559_4, c8_559_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_561_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_125l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_561_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_125l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_561_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_125l) (hubSubn 8 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_561_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_125l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_561_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_125l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_561 :
    hubcapFit theRedpart rf8 p8_125l
    (Hubcap.one 0 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_561_1, c8_561_2, c8_561_3, c8_561_4, c8_561_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_562_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_562_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_124l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_562_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_124l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_562_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_124l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_562_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_124l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_562 :
    hubcapFit theRedpart rf8 p8_124l
    (Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_562_1, c8_562_2, c8_562_3, c8_562_4, c8_562_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_564_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_564_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_123l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_564_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_123l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_564_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_123l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_564_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_123l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_564 :
    hubcapFit theRedpart rf8 p8_123l
    (Hubcap.one 0 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_564_1, c8_564_2, c8_564_3, c8_564_4, c8_564_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_582r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_582r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_582r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_583_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_582r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_583 :
    hubcapFit theRedpart rf8 p8_582r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_583_1, c8_583_2, c8_583_3, c8_583_4, c8_583_5, c8_583_6, c8_583_7, c8_583_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_589r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_589r) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_590_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_589r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_590 :
    hubcapFit theRedpart rf8 p8_589r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_590_1, c8_590_2, c8_590_3, c8_590_4, c8_590_5, c8_590_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_589l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_591_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_589l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_591 :
    hubcapFit theRedpart rf8 p8_589l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_591_1, c8_591_2, c8_591_3, c8_591_4, c8_591_5, c8_591_6, c8_591_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_587l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_587l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_593_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_587l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_593 :
    hubcapFit theRedpart rf8 p8_587l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_593_1, c8_593_2, c8_593_3, c8_593_4, c8_593_5, c8_593_6, c8_593_7, c8_593_8]

end FourColor

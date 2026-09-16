import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 13 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_714l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_714l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_714l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_714l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_727_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_727 :
    hubcapFit theRedpart rf7 p7_714l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_727_1, c7_727_2, c7_727_3, c7_727_4, c7_727_5, c7_727_6, c7_727_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_713l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_713l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_713l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_729_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_713l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_729 :
    hubcapFit theRedpart rf7 p7_713l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_729_1, c7_729_2, c7_729_3, c7_729_4, c7_729_5, c7_729_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_730_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_730 :
    hubcapFit theRedpart rf7 p7_712l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_730_1, c7_730_2, c7_730_3, c7_730_4, c7_730_5, c7_730_6, c7_730_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_710l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_710l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_732_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_710l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_732 :
    hubcapFit theRedpart rf7 p7_710l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_732_1, c7_732_2, c7_732_3, c7_732_4, c7_732_5, c7_732_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_708l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_708l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_734_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_708l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_734 :
    hubcapFit theRedpart rf7 p7_708l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_734_1, c7_734_2, c7_734_3, c7_734_4, c7_734_5, c7_734_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_743r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_743r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_743r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_743r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_743r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_743r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_744_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_743r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_744 :
    hubcapFit theRedpart rf7 p7_743r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_744_1, c7_744_2, c7_744_3, c7_744_4, c7_744_5, c7_744_6, c7_744_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_745_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_743l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_745_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_743l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_745_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_743l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_745_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_743l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_745_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_743l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_745 :
    hubcapFit theRedpart rf7 p7_743l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_745_1, c7_745_2, c7_745_3, c7_745_4, c7_745_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_747_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_742l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_747_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_742l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_747_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_742l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_747_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_742l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_747_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_742l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_747 :
    hubcapFit theRedpart rf7 p7_742l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_747_1, c7_747_2, c7_747_3, c7_747_4, c7_747_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_748_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_741l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_748_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_741l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_748_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_741l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_748_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_741l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_748_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_741l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_748 :
    hubcapFit theRedpart rf7 p7_741l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_748_1, c7_748_2, c7_748_3, c7_748_4, c7_748_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_750_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_750_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_740l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_750_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_740l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_750_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_740l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_750_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_740l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_750 :
    hubcapFit theRedpart rf7 p7_740l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_750_1, c7_750_2, c7_750_3, c7_750_4, c7_750_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_739l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_739l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_739l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_739l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_739l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_751_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_739l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_751 :
    hubcapFit theRedpart rf7 p7_739l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_751_1, c7_751_2, c7_751_3, c7_751_4, c7_751_5, c7_751_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_753_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_738l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_753_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_738l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_753_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_738l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_753_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_738l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_753_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_738l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_753 :
    hubcapFit theRedpart rf7 p7_738l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_753_1, c7_753_2, c7_753_3, c7_753_4, c7_753_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_737l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_737l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_737l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_737l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_737l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_754_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_737l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_754 :
    hubcapFit theRedpart rf7 p7_737l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_754_1, c7_754_2, c7_754_3, c7_754_4, c7_754_5, c7_754_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_762_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_761r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_762_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_761r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_762_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_761r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_762_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_761r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_762_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_761r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_762 :
    hubcapFit theRedpart rf7 p7_761r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_762_1, c7_762_2, c7_762_3, c7_762_4, c7_762_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_763_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_761l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_763_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_761l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_763_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_761l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_763_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_761l) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_763_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_761l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_763 :
    hubcapFit theRedpart rf7 p7_761l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_763_1, c7_763_2, c7_763_3, c7_763_4, c7_763_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_765_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_760l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_765_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_760l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_765_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_760l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_765_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_760l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_765_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_760l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_765 :
    hubcapFit theRedpart rf7 p7_760l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_765_1, c7_765_2, c7_765_3, c7_765_4, c7_765_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_759l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_759l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_759l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_759l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_759l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_766_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_759l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_766 :
    hubcapFit theRedpart rf7 p7_759l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_766_1, c7_766_2, c7_766_3, c7_766_4, c7_766_5, c7_766_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_758l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_758l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_758l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_758l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_758l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_768_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_758l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_768 :
    hubcapFit theRedpart rf7 p7_758l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_768_1, c7_768_2, c7_768_3, c7_768_4, c7_768_5, c7_768_6]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 16 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_695r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_695r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_695r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_695r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_695r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_695r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_698_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_695r) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_698 :
    hubcapFit theRedpart rf9 p9_695r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_698_1, c9_698_2, c9_698_3, c9_698_4, c9_698_5, c9_698_6, c9_698_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_728r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_728r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_728r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_728r) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_728r) (hubSubn 9 8 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_729_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_728r) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_729 :
    hubcapFit theRedpart rf9 p9_728r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 4 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_729_1, c9_729_2, c9_729_3, c9_729_4, c9_729_5, c9_729_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_728l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_728l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_728l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_728l) (hubSubn 9 8 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_730_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_728l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_730 :
    hubcapFit theRedpart rf9 p9_728l
    (Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 8 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_730_1, c9_730_2, c9_730_3, c9_730_4, c9_730_5, c9_730_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_732_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_727l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_732_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_727l) (hubSubn 9 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_732_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_727l) (hubSubn 9 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_732_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_727l) (hubSubn 9 7 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_732_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_727l) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_732 :
    hubcapFit theRedpart rf9 p9_727l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 5 6 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 7 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_732_1, c9_732_2, c9_732_3, c9_732_4, c9_732_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_748r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_748r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_748r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_748r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_748r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_748r) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_749_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_748r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_749 :
    hubcapFit theRedpart rf9 p9_748r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_749_1, c9_749_2, c9_749_3, c9_749_4, c9_749_5, c9_749_6, c9_749_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_748l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_748l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_748l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_748l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_750_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_748l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_750 :
    hubcapFit theRedpart rf9 p9_748l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_750_1, c9_750_2, c9_750_3, c9_750_4, c9_750_5, c9_750_6, c9_750_7, c9_750_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_746l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_746l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_746l) (hubSubn 9 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_752_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_746l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_752 :
    hubcapFit theRedpart rf9 p9_746l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_752_1, c9_752_2, c9_752_3, c9_752_4, c9_752_5, c9_752_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_754_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_744l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_754 :
    hubcapFit theRedpart rf9 p9_744l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_754_1, c9_754_2, c9_754_3, c9_754_4, c9_754_5, c9_754_6, c9_754_7, c9_754_8, c9_754_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_756_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_756 :
    hubcapFit theRedpart rf9 p9_742l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_756_1, c9_756_2, c9_756_3, c9_756_4, c9_756_5, c9_756_6, c9_756_7, c9_756_8, c9_756_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_758_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_758 :
    hubcapFit theRedpart rf9 p9_740l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_758_1, c9_758_2, c9_758_3, c9_758_4, c9_758_5, c9_758_6, c9_758_7, c9_758_8, c9_758_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_760_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_760 :
    hubcapFit theRedpart rf9 p9_738l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_760_1, c9_760_2, c9_760_3, c9_760_4, c9_760_5, c9_760_6, c9_760_7, c9_760_8, c9_760_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_762_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_736l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_762 :
    hubcapFit theRedpart rf9 p9_736l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_762_1, c9_762_2, c9_762_3, c9_762_4, c9_762_5, c9_762_6, c9_762_7, c9_762_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_770_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_769r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_770_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_769r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_770_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_769r) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_770_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_769r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_770_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_769r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_770 :
    hubcapFit theRedpart rf9 p9_769r
    (Hubcap.one 2 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_770_1, c9_770_2, c9_770_3, c9_770_4, c9_770_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_769l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_769l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_769l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_771_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_769l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_771 :
    hubcapFit theRedpart rf9 p9_769l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_771_1, c9_771_2, c9_771_3, c9_771_4, c9_771_5, c9_771_6, c9_771_7, c9_771_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_768l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_768l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_773_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_768l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_773 :
    hubcapFit theRedpart rf9 p9_768l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_773_1, c9_773_2, c9_773_3, c9_773_4, c9_773_5, c9_773_6, c9_773_7]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 17 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_767l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_767l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_767l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_767l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_767l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_775_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_767l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_775 :
    hubcapFit theRedpart rf9 p9_767l
    (Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_775_1, c9_775_2, c9_775_3, c9_775_4, c9_775_5, c9_775_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_766l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_766l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_766l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_766l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_776_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_766l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_776 :
    hubcapFit theRedpart rf9 p9_766l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_776_1, c9_776_2, c9_776_3, c9_776_4, c9_776_5, c9_776_6, c9_776_7, c9_776_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_708l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_708l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_778_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_708l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_778 :
    hubcapFit theRedpart rf9 p9_708l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 0 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_778_1, c9_778_2, c9_778_3, c9_778_4, c9_778_5, c9_778_6, c9_778_7, c9_778_8, c9_778_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_780_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_780 :
    hubcapFit theRedpart rf9 p9_707l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_780_1, c9_780_2, c9_780_3, c9_780_4, c9_780_5, c9_780_6, c9_780_7, c9_780_8, c9_780_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_706l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_782_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_782 :
    hubcapFit theRedpart rf9 p9_706l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_782_1, c9_782_2, c9_782_3, c9_782_4, c9_782_5, c9_782_6, c9_782_7, c9_782_8, c9_782_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_705l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_784_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_784 :
    hubcapFit theRedpart rf9 p9_705l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_784_1, c9_784_2, c9_784_3, c9_784_4, c9_784_5, c9_784_6, c9_784_7, c9_784_8, c9_784_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_704l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_704l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_786_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_704l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_786 :
    hubcapFit theRedpart rf9 p9_704l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_786_1, c9_786_2, c9_786_3, c9_786_4, c9_786_5, c9_786_6, c9_786_7, c9_786_8, c9_786_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_703l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_703l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_703l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_788_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_703l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_788 :
    hubcapFit theRedpart rf9 p9_703l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_788_1, c9_788_2, c9_788_3, c9_788_4, c9_788_5, c9_788_6, c9_788_7, c9_788_8, c9_788_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_807r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_807r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_807r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_807r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_807r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_807r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_808_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_807r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_808 :
    hubcapFit theRedpart rf9 p9_807r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_808_1, c9_808_2, c9_808_3, c9_808_4, c9_808_5, c9_808_6, c9_808_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_807l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_807l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_807l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_807l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_807l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_807l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_809_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_807l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_809 :
    hubcapFit theRedpart rf9 p9_807l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_809_1, c9_809_2, c9_809_3, c9_809_4, c9_809_5, c9_809_6, c9_809_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_806l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_806l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_806l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_806l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_806l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_806l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_811_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_806l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_811 :
    hubcapFit theRedpart rf9 p9_806l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_811_1, c9_811_2, c9_811_3, c9_811_4, c9_811_5, c9_811_6, c9_811_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_805l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_805l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_805l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_805l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_805l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_805l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_805l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_813_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_805l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_813 :
    hubcapFit theRedpart rf9 p9_805l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_813_1, c9_813_2, c9_813_3, c9_813_4, c9_813_5, c9_813_6, c9_813_7, c9_813_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_804l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_804l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_804l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_804l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_804l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_804l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_815_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_804l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_815 :
    hubcapFit theRedpart rf9 p9_804l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_815_1, c9_815_2, c9_815_3, c9_815_4, c9_815_5, c9_815_6, c9_815_7, c9_815_8]

end FourColor

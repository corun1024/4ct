import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 89 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4754r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4754r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4754r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4754r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4754r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4754r) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4755_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4754r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4755 :
    hubcapFit theRedpart rf7 p7_4754r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4755_1, c7_4755_2, c7_4755_3, c7_4755_4, c7_4755_5, c7_4755_6, c7_4755_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4754l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4754l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4754l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4754l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4754l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4756_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4754l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4756 :
    hubcapFit theRedpart rf7 p7_4754l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4756_1, c7_4756_2, c7_4756_3, c7_4756_4, c7_4756_5, c7_4756_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4753l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4753l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4753l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4753l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4753l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4758_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4753l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4758 :
    hubcapFit theRedpart rf7 p7_4753l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4758_1, c7_4758_2, c7_4758_3, c7_4758_4, c7_4758_5, c7_4758_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4747l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4747l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4747l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4747l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4747l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4760_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4747l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4760 :
    hubcapFit theRedpart rf7 p7_4747l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4760_1, c7_4760_2, c7_4760_3, c7_4760_4, c7_4760_5, c7_4760_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4746l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4746l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4746l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4746l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4746l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4761_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4746l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4761 :
    hubcapFit theRedpart rf7 p7_4746l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4761_1, c7_4761_2, c7_4761_3, c7_4761_4, c7_4761_5, c7_4761_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4771r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4771r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4771r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4771r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4771r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4772_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4771r) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4772 :
    hubcapFit theRedpart rf7 p7_4771r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4772_1, c7_4772_2, c7_4772_3, c7_4772_4, c7_4772_5, c7_4772_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4771l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4771l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4771l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4771l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4771l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4771l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4773_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4771l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4773 :
    hubcapFit theRedpart rf7 p7_4771l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4773_1, c7_4773_2, c7_4773_3, c7_4773_4, c7_4773_5, c7_4773_6, c7_4773_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4770l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4770l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4770l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4770l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4770l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4775_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4770l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4775 :
    hubcapFit theRedpart rf7 p7_4770l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4775_1, c7_4775_2, c7_4775_3, c7_4775_4, c7_4775_5, c7_4775_6, c7_4775_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4768l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4768l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4768l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4777_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4768l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4777 :
    hubcapFit theRedpart rf7 p7_4768l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4777_1, c7_4777_2, c7_4777_3, c7_4777_4, c7_4777_5, c7_4777_6, c7_4777_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4767l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4767l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4767l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4767l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4767l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4779_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4767l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4779 :
    hubcapFit theRedpart rf7 p7_4767l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4779_1, c7_4779_2, c7_4779_3, c7_4779_4, c7_4779_5, c7_4779_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4766l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4766l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4780_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4766l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4780 :
    hubcapFit theRedpart rf7 p7_4766l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4780_1, c7_4780_2, c7_4780_3, c7_4780_4, c7_4780_5, c7_4780_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4784r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4784r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4784r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4784r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4784r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4785_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4784r) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4785 :
    hubcapFit theRedpart rf7 p7_4784r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4785_1, c7_4785_2, c7_4785_3, c7_4785_4, c7_4785_5, c7_4785_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4786_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4786 :
    hubcapFit theRedpart rf7 p7_4784l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4786_1, c7_4786_2, c7_4786_3, c7_4786_4, c7_4786_5, c7_4786_6, c7_4786_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4788_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4783l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4788 :
    hubcapFit theRedpart rf7 p7_4783l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4788_1, c7_4788_2, c7_4788_3, c7_4788_4, c7_4788_5, c7_4788_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4782l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4782l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4782l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4782l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4782l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4782l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4789_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4782l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4789 :
    hubcapFit theRedpart rf7 p7_4782l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4789_1, c7_4789_2, c7_4789_3, c7_4789_4, c7_4789_5, c7_4789_6, c7_4789_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4764l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4791_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4764l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4791 :
    hubcapFit theRedpart rf7 p7_4764l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4791_1, c7_4791_2, c7_4791_3, c7_4791_4, c7_4791_5, c7_4791_6]

end FourColor

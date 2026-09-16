import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 97 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4858r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4858r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4858r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4858r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4858r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4858r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4859_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4858r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4859 :
    hubcapFit theRedpart rf8 p8_4858r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4859_1, c8_4859_2, c8_4859_3, c8_4859_4, c8_4859_5, c8_4859_6, c8_4859_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4858l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4860_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4858l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4860 :
    hubcapFit theRedpart rf8 p8_4858l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4860_1, c8_4860_2, c8_4860_3, c8_4860_4, c8_4860_5, c8_4860_6, c8_4860_7, c8_4860_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4857l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4857l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4857l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4857l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4857l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4862_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4857l) (hubSubn 8 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4862 :
    hubcapFit theRedpart rf8 p8_4857l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4862_1, c8_4862_2, c8_4862_3, c8_4862_4, c8_4862_5, c8_4862_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4855l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4855l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4855l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4855l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4855l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4864_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4864 :
    hubcapFit theRedpart rf8 p8_4855l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4864_1, c8_4864_2, c8_4864_3, c8_4864_4, c8_4864_5, c8_4864_6, c8_4864_7, c8_4864_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4854l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4854l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4854l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4854l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4866_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4854l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4866 :
    hubcapFit theRedpart rf8 p8_4854l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4866_1, c8_4866_2, c8_4866_3, c8_4866_4, c8_4866_5, c8_4866_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4853l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4853l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4867_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4867 :
    hubcapFit theRedpart rf8 p8_4853l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4867_1, c8_4867_2, c8_4867_3, c8_4867_4, c8_4867_5, c8_4867_6, c8_4867_7, c8_4867_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4852l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4852l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4869_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4852l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4869 :
    hubcapFit theRedpart rf8 p8_4852l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4869_1, c8_4869_2, c8_4869_3, c8_4869_4, c8_4869_5, c8_4869_6, c8_4869_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4851l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4851l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4851l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4871_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4851l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4871 :
    hubcapFit theRedpart rf8 p8_4851l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4871_1, c8_4871_2, c8_4871_3, c8_4871_4, c8_4871_5, c8_4871_6, c8_4871_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4875r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4875r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4875r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4875r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4875r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4875r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4876_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4875r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4876 :
    hubcapFit theRedpart rf8 p8_4875r
    (Hubcap.one 1 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4876_1, c8_4876_2, c8_4876_3, c8_4876_4, c8_4876_5, c8_4876_6, c8_4876_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4875l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4875l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4875l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4875l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4877_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4875l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4877 :
    hubcapFit theRedpart rf8 p8_4875l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4877_1, c8_4877_2, c8_4877_3, c8_4877_4, c8_4877_5, c8_4877_6, c8_4877_7, c8_4877_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4874l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4874l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4874l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4874l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4874l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4874l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4879_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4874l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4879 :
    hubcapFit theRedpart rf8 p8_4874l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4879_1, c8_4879_2, c8_4879_3, c8_4879_4, c8_4879_5, c8_4879_6, c8_4879_7, c8_4879_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4873l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4873l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4873l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4873l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4881_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4873l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4881 :
    hubcapFit theRedpart rf8 p8_4873l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4881_1, c8_4881_2, c8_4881_3, c8_4881_4, c8_4881_5, c8_4881_6, c8_4881_7, c8_4881_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4889r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4889r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4889r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4889r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4889r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4889r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4890_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4889r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4890 :
    hubcapFit theRedpart rf8 p8_4889r
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4890_1, c8_4890_2, c8_4890_3, c8_4890_4, c8_4890_5, c8_4890_6, c8_4890_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4889l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4889l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4889l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4889l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4889l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4889l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4891_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4891 :
    hubcapFit theRedpart rf8 p8_4889l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4891_1, c8_4891_2, c8_4891_3, c8_4891_4, c8_4891_5, c8_4891_6, c8_4891_7, c8_4891_8]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 110 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5479l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5479l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5479l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5479l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5479l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5487_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5479l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5487 :
    hubcapFit theRedpart rf8 p8_5479l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5487_1, c8_5487_2, c8_5487_3, c8_5487_4, c8_5487_5, c8_5487_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5493r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5493r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5493r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5493r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5493r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5493r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5494_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5493r) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5494 :
    hubcapFit theRedpart rf8 p8_5493r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5494_1, c8_5494_2, c8_5494_3, c8_5494_4, c8_5494_5, c8_5494_6, c8_5494_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5495_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5495_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5493l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5495_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5493l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5495_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5493l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5495_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5493l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5495 :
    hubcapFit theRedpart rf8 p8_5493l
    (Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5495_1, c8_5495_2, c8_5495_3, c8_5495_4, c8_5495_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5497_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5491l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5497_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5497_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5491l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5497_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5491l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5497_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5491l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5497 :
    hubcapFit theRedpart rf8 p8_5491l
    (Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5497_1, c8_5497_2, c8_5497_3, c8_5497_4, c8_5497_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5459l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5459l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5459l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5459l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5499_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5459l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5499 :
    hubcapFit theRedpart rf8 p8_5459l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5499_1, c8_5499_2, c8_5499_3, c8_5499_4, c8_5499_5, c8_5499_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5458l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5458l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5458l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5458l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5458l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5501_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5458l) (hubSubn 8 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5501 :
    hubcapFit theRedpart rf8 p8_5458l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5501_1, c8_5501_2, c8_5501_3, c8_5501_4, c8_5501_5, c8_5501_6]

end FourColor

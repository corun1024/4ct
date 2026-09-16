import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 96 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5084l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5084l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5084l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5084l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5084l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5105_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5084l) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5105 :
    hubcapFit theRedpart rf7 p7_5084l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5105_1, c7_5105_2, c7_5105_3, c7_5105_4, c7_5105_5, c7_5105_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5083l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5107_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5083l) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5107 :
    hubcapFit theRedpart rf7 p7_5083l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 4 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5107_1, c7_5107_2, c7_5107_3, c7_5107_4, c7_5107_5, c7_5107_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5110r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5110r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5110r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5110r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5110r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5111_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5110r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5111 :
    hubcapFit theRedpart rf7 p7_5110r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5111_1, c7_5111_2, c7_5111_3, c7_5111_4, c7_5111_5, c7_5111_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5110l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5110l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5110l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5110l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5110l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5112_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5110l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5112 :
    hubcapFit theRedpart rf7 p7_5110l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5112_1, c7_5112_2, c7_5112_3, c7_5112_4, c7_5112_5, c7_5112_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5109l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5109l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5109l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5109l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5109l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5109l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5114_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5109l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5114 :
    hubcapFit theRedpart rf7 p7_5109l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5114_1, c7_5114_2, c7_5114_3, c7_5114_4, c7_5114_5, c7_5114_6, c7_5114_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5108l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5108l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5108l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5108l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5108l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5116_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5108l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5116 :
    hubcapFit theRedpart rf7 p7_5108l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5116_1, c7_5116_2, c7_5116_3, c7_5116_4, c7_5116_5, c7_5116_6, c7_5116_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5081l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5081l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5081l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5081l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5081l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5119_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5081l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5119 :
    hubcapFit theRedpart rf7 p7_5081l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5119_1, c7_5119_2, c7_5119_3, c7_5119_4, c7_5119_5, c7_5119_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5080l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5080l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5120_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5080l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5120 :
    hubcapFit theRedpart rf7 p7_5080l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5120_1, c7_5120_2, c7_5120_3, c7_5120_4, c7_5120_5, c7_5120_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5134r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5134r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5134r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5134r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5134r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5134r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5135_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5134r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5135 :
    hubcapFit theRedpart rf7 p7_5134r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5135_1, c7_5135_2, c7_5135_3, c7_5135_4, c7_5135_5, c7_5135_6, c7_5135_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5134l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5134l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5134l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5136_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5134l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5136 :
    hubcapFit theRedpart rf7 p7_5134l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5136_1, c7_5136_2, c7_5136_3, c7_5136_4, c7_5136_5, c7_5136_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5133l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5133l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5133l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5133l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5133l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5138_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5133l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5138 :
    hubcapFit theRedpart rf7 p7_5133l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5138_1, c7_5138_2, c7_5138_3, c7_5138_4, c7_5138_5, c7_5138_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5132l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5139_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5139 :
    hubcapFit theRedpart rf7 p7_5132l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5139_1, c7_5139_2, c7_5139_3, c7_5139_4, c7_5139_5, c7_5139_6, c7_5139_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5131l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5131l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5131l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5131l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5131l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5131l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5141_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5131l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5141 :
    hubcapFit theRedpart rf7 p7_5131l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5141_1, c7_5141_2, c7_5141_3, c7_5141_4, c7_5141_5, c7_5141_6, c7_5141_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5143_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5130l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5143_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5130l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5143_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5130l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5143_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5130l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5143_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5130l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5143 :
    hubcapFit theRedpart rf7 p7_5130l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5143_1, c7_5143_2, c7_5143_3, c7_5143_4, c7_5143_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5129l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5129l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5129l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5129l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5129l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5144_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5129l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5144 :
    hubcapFit theRedpart rf7 p7_5129l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5144_1, c7_5144_2, c7_5144_3, c7_5144_4, c7_5144_5, c7_5144_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5146_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5146_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5146_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5127l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5146_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5127l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5146_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5127l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5146 :
    hubcapFit theRedpart rf7 p7_5127l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5146_1, c7_5146_2, c7_5146_3, c7_5146_4, c7_5146_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5150r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5150r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5150r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5150r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5150r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5151_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5150r) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5151 :
    hubcapFit theRedpart rf7 p7_5150r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5151_1, c7_5151_2, c7_5151_3, c7_5151_4, c7_5151_5, c7_5151_6]

end FourColor

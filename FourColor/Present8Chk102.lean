import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 102 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5082l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5082l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5082l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5082l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5082l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5082l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5090_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5082l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5090 :
    hubcapFit theRedpart rf8 p8_5082l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5090_1, c8_5090_2, c8_5090_3, c8_5090_4, c8_5090_5, c8_5090_6, c8_5090_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5061l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5061l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5061l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5061l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5061l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5092_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5061l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5092 :
    hubcapFit theRedpart rf8 p8_5061l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5092_1, c8_5092_2, c8_5092_3, c8_5092_4, c8_5092_5, c8_5092_6, c8_5092_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5060l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5060l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5060l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5060l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5094_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5060l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5094 :
    hubcapFit theRedpart rf8 p8_5060l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5094_1, c8_5094_2, c8_5094_3, c8_5094_4, c8_5094_5, c8_5094_6, c8_5094_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5106r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5106r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5106r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5106r) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5106r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5106r) (hubSubn 8 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5107_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5106r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5107 :
    hubcapFit theRedpart rf8 p8_5106r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5107_1, c8_5107_2, c8_5107_3, c8_5107_4, c8_5107_5, c8_5107_6, c8_5107_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5106l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5106l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5106l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5106l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5106l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5106l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5108_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5106l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5108 :
    hubcapFit theRedpart rf8 p8_5106l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5108_1, c8_5108_2, c8_5108_3, c8_5108_4, c8_5108_5, c8_5108_6, c8_5108_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5104l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5104l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5104l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5110_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5104l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5110 :
    hubcapFit theRedpart rf8 p8_5104l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5110_1, c8_5110_2, c8_5110_3, c8_5110_4, c8_5110_5, c8_5110_6, c8_5110_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5121r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5121r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5121r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5122_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5121r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5122 :
    hubcapFit theRedpart rf8 p8_5121r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5122_1, c8_5122_2, c8_5122_3, c8_5122_4, c8_5122_5, c8_5122_6, c8_5122_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5121l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5121l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5123_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5123 :
    hubcapFit theRedpart rf8 p8_5121l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5123_1, c8_5123_2, c8_5123_3, c8_5123_4, c8_5123_5, c8_5123_6, c8_5123_7, c8_5123_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5119l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5119l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5119l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5119l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5119l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5119l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5125_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5119l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5125 :
    hubcapFit theRedpart rf8 p8_5119l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5125_1, c8_5125_2, c8_5125_3, c8_5125_4, c8_5125_5, c8_5125_6, c8_5125_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5118l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5118l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5127_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5118l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5127 :
    hubcapFit theRedpart rf8 p8_5118l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5127_1, c8_5127_2, c8_5127_3, c8_5127_4, c8_5127_5, c8_5127_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5116l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5116l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5116l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5116l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5116l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5116l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5129_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5116l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5129 :
    hubcapFit theRedpart rf8 p8_5116l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5129_1, c8_5129_2, c8_5129_3, c8_5129_4, c8_5129_5, c8_5129_6, c8_5129_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5114l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5114l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5114l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5114l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5114l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5114l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5131_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5114l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5131 :
    hubcapFit theRedpart rf8 p8_5114l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5131_1, c8_5131_2, c8_5131_3, c8_5131_4, c8_5131_5, c8_5131_6, c8_5131_7, c8_5131_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5112l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5112l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5112l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5133_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5112l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5133 :
    hubcapFit theRedpart rf8 p8_5112l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5133_1, c8_5133_2, c8_5133_3, c8_5133_4, c8_5133_5, c8_5133_6, c8_5133_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5136_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5136_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5099l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5136_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5099l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5136_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5099l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5136_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5099l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5136 :
    hubcapFit theRedpart rf8 p8_5099l
    (Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5136_1, c8_5136_2, c8_5136_3, c8_5136_4, c8_5136_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5098l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5098l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5098l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5098l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5098l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5098l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5137_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5098l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5137 :
    hubcapFit theRedpart rf8 p8_5098l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5137_1, c8_5137_2, c8_5137_3, c8_5137_4, c8_5137_5, c8_5137_6, c8_5137_7]

end FourColor

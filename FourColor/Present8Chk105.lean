import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 105 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5229l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5229l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5229l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5229l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5229l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5229l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5237_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5229l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5237 :
    hubcapFit theRedpart rf8 p8_5229l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5237_1, c8_5237_2, c8_5237_3, c8_5237_4, c8_5237_5, c8_5237_6, c8_5237_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5228l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5228l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5228l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5228l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5228l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5239_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5239 :
    hubcapFit theRedpart rf8 p8_5228l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5239_1, c8_5239_2, c8_5239_3, c8_5239_4, c8_5239_5, c8_5239_6, c8_5239_7, c8_5239_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5243r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5243r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5243r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5243r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5243r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5243r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5244_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5243r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5244 :
    hubcapFit theRedpart rf8 p8_5243r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5244_1, c8_5244_2, c8_5244_3, c8_5244_4, c8_5244_5, c8_5244_6, c8_5244_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5243l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5243l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5243l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5245_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5243l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5245 :
    hubcapFit theRedpart rf8 p8_5243l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5245_1, c8_5245_2, c8_5245_3, c8_5245_4, c8_5245_5, c8_5245_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5198l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5198l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5198l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5198l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5248_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5198l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5248 :
    hubcapFit theRedpart rf8 p8_5198l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5248_1, c8_5248_2, c8_5248_3, c8_5248_4, c8_5248_5, c8_5248_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5262r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5262r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5262r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5262r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5262r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5263_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5262r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5263 :
    hubcapFit theRedpart rf8 p8_5262r
    (Hubcap.one 0 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5263_1, c8_5263_2, c8_5263_3, c8_5263_4, c8_5263_5, c8_5263_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5262l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5262l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5262l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5264_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5262l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5264 :
    hubcapFit theRedpart rf8 p8_5262l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5264_1, c8_5264_2, c8_5264_3, c8_5264_4, c8_5264_5, c8_5264_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5261l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5261l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5266_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5261l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5266 :
    hubcapFit theRedpart rf8 p8_5261l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5266_1, c8_5266_2, c8_5266_3, c8_5266_4, c8_5266_5, c8_5266_6, c8_5266_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5269r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5269r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5269r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5269r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5269r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5269r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5270_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5269r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5270 :
    hubcapFit theRedpart rf8 p8_5269r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5270_1, c8_5270_2, c8_5270_3, c8_5270_4, c8_5270_5, c8_5270_6, c8_5270_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5269l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5269l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5269l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5269l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5269l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5271_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5269l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5271 :
    hubcapFit theRedpart rf8 p8_5269l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5271_1, c8_5271_2, c8_5271_3, c8_5271_4, c8_5271_5, c8_5271_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5268l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5268l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5268l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5268l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5268l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5273_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5268l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5273 :
    hubcapFit theRedpart rf8 p8_5268l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5273_1, c8_5273_2, c8_5273_3, c8_5273_4, c8_5273_5, c8_5273_6, c8_5273_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5258l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5258l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5258l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5258l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5275_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5258l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5275 :
    hubcapFit theRedpart rf8 p8_5258l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5275_1, c8_5275_2, c8_5275_3, c8_5275_4, c8_5275_5, c8_5275_6, c8_5275_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5257l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5257l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5257l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5257l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5257l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5277_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5257l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5277 :
    hubcapFit theRedpart rf8 p8_5257l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5277_1, c8_5277_2, c8_5277_3, c8_5277_4, c8_5277_5, c8_5277_6, c8_5277_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5281r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5281r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5281r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5281r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5281r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5281r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5281r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5282_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5281r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5282 :
    hubcapFit theRedpart rf8 p8_5281r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5282_1, c8_5282_2, c8_5282_3, c8_5282_4, c8_5282_5, c8_5282_6, c8_5282_7, c8_5282_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5281l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5281l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5281l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5283_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5281l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5283 :
    hubcapFit theRedpart rf8 p8_5281l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5283_1, c8_5283_2, c8_5283_3, c8_5283_4, c8_5283_5, c8_5283_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5280l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5280l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5280l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5285_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5280l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5285 :
    hubcapFit theRedpart rf8 p8_5280l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5285_1, c8_5285_2, c8_5285_3, c8_5285_4, c8_5285_5, c8_5285_6, c8_5285_7]

end FourColor

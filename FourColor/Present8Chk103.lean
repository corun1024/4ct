import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 103 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5143r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5143r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5143r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5143r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5143r) (hubSubn 8 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5144_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5143r) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5144 :
    hubcapFit theRedpart rf8 p8_5143r
    (Hubcap.one 0 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5144_1, c8_5144_2, c8_5144_3, c8_5144_4, c8_5144_5, c8_5144_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5143l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5143l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5143l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5143l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5143l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5145_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5143l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5145 :
    hubcapFit theRedpart rf8 p8_5143l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5145_1, c8_5145_2, c8_5145_3, c8_5145_4, c8_5145_5, c8_5145_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5142l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5142l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5142l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5142l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5142l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5147_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5142l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5147 :
    hubcapFit theRedpart rf8 p8_5142l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5147_1, c8_5147_2, c8_5147_3, c8_5147_4, c8_5147_5, c8_5147_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5141l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5141l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5141l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5141l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5141l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5141l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5148_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5141l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5148 :
    hubcapFit theRedpart rf8 p8_5141l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5148_1, c8_5148_2, c8_5148_3, c8_5148_4, c8_5148_5, c8_5148_6, c8_5148_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5140l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5140l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5140l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5140l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5150_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5140l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5150 :
    hubcapFit theRedpart rf8 p8_5140l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5150_1, c8_5150_2, c8_5150_3, c8_5150_4, c8_5150_5, c8_5150_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5153l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5153l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5154_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5153l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5154 :
    hubcapFit theRedpart rf8 p8_5153l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5154_1, c8_5154_2, c8_5154_3, c8_5154_4, c8_5154_5, c8_5154_6, c8_5154_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5153r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5153r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5153r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5153r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5153r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5153r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5156_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5153r) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5156 :
    hubcapFit theRedpart rf8 p8_5153r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5156_1, c8_5156_2, c8_5156_3, c8_5156_4, c8_5156_5, c8_5156_6, c8_5156_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5160l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5160l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5160l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5160l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5161_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5160l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5161 :
    hubcapFit theRedpart rf8 p8_5160l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5161_1, c8_5161_2, c8_5161_3, c8_5161_4, c8_5161_5, c8_5161_6, c8_5161_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5160r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5160r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5160r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5160r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5160r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5160r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5163_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5160r) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5163 :
    hubcapFit theRedpart rf8 p8_5160r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5163_1, c8_5163_2, c8_5163_3, c8_5163_4, c8_5163_5, c8_5163_6, c8_5163_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5166l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5166l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5167_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5166l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5167 :
    hubcapFit theRedpart rf8 p8_5166l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5167_1, c8_5167_2, c8_5167_3, c8_5167_4, c8_5167_5, c8_5167_6, c8_5167_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5166r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5166r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5166r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5166r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5166r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5166r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5169_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5166r) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5169 :
    hubcapFit theRedpart rf8 p8_5166r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5169_1, c8_5169_2, c8_5169_3, c8_5169_4, c8_5169_5, c8_5169_6, c8_5169_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5182r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5182r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5183_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5182r) (hubSubn 8 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5183 :
    hubcapFit theRedpart rf8 p8_5182r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5183_1, c8_5183_2, c8_5183_3, c8_5183_4, c8_5183_5, c8_5183_6, c8_5183_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5182l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5182l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5184_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5182l) (hubSubn 8 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5184 :
    hubcapFit theRedpart rf8 p8_5182l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5184_1, c8_5184_2, c8_5184_3, c8_5184_4, c8_5184_5, c8_5184_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5181l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5186_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5181l) (hubSubn 8 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5186 :
    hubcapFit theRedpart rf8 p8_5181l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5186_1, c8_5186_2, c8_5186_3, c8_5186_4, c8_5186_5, c8_5186_6, c8_5186_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5180l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5180l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5188_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5180l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5188 :
    hubcapFit theRedpart rf8 p8_5180l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5188_1, c8_5188_2, c8_5188_3, c8_5188_4, c8_5188_5, c8_5188_6, c8_5188_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5190_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5179l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5190_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5179l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5190_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5179l) (hubSubn 8 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5190_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5179l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5190_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5179l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5190 :
    hubcapFit theRedpart rf8 p8_5179l
    (Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5190_1, c8_5190_2, c8_5190_3, c8_5190_4, c8_5190_5]

end FourColor

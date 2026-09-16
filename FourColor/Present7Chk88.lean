import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 88 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4698l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4698l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4708_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4698l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4708 :
    hubcapFit theRedpart rf7 p7_4698l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4708_1, c7_4708_2, c7_4708_3, c7_4708_4, c7_4708_5, c7_4708_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4712r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4712r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4712r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4712r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4712r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4712r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4713_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4712r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4713 :
    hubcapFit theRedpart rf7 p7_4712r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4713_1, c7_4713_2, c7_4713_3, c7_4713_4, c7_4713_5, c7_4713_6, c7_4713_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4712l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4714_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4712l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4714 :
    hubcapFit theRedpart rf7 p7_4712l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4714_1, c7_4714_2, c7_4714_3, c7_4714_4, c7_4714_5, c7_4714_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4711l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4711l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4711l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4711l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4711l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4716_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4711l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4716 :
    hubcapFit theRedpart rf7 p7_4711l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4716_1, c7_4716_2, c7_4716_3, c7_4716_4, c7_4716_5, c7_4716_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4717_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4717_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4717_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4717_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4710l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4717_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4710l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4717 :
    hubcapFit theRedpart rf7 p7_4710l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4717_1, c7_4717_2, c7_4717_3, c7_4717_4, c7_4717_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4709l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4709l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4719_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4709l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4719 :
    hubcapFit theRedpart rf7 p7_4709l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4719_1, c7_4719_2, c7_4719_3, c7_4719_4, c7_4719_5, c7_4719_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4730r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4730r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4730r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4730r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4730r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4730r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4731_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4730r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4731 :
    hubcapFit theRedpart rf7 p7_4730r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4731_1, c7_4731_2, c7_4731_3, c7_4731_4, c7_4731_5, c7_4731_6, c7_4731_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4730l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4730l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4732_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4730l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4732 :
    hubcapFit theRedpart rf7 p7_4730l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4732_1, c7_4732_2, c7_4732_3, c7_4732_4, c7_4732_5, c7_4732_6, c7_4732_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4729l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4729l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4734_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4729l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4734 :
    hubcapFit theRedpart rf7 p7_4729l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4734_1, c7_4734_2, c7_4734_3, c7_4734_4, c7_4734_5, c7_4734_6, c7_4734_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4726l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4726l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4726l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4726l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4726l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4736_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4726l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4736 :
    hubcapFit theRedpart rf7 p7_4726l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4736_1, c7_4736_2, c7_4736_3, c7_4736_4, c7_4736_5, c7_4736_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4725l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4725l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4725l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4725l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4725l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4738_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4725l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4738 :
    hubcapFit theRedpart rf7 p7_4725l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4738_1, c7_4738_2, c7_4738_3, c7_4738_4, c7_4738_5, c7_4738_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4739_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4724l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4739_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4724l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4739_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4724l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4739_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4724l) (hubSubn 7 6 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4739_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4724l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4739 :
    hubcapFit theRedpart rf7 p7_4724l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4739_1, c7_4739_2, c7_4739_3, c7_4739_4, c7_4739_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4741_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4723l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4741_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4723l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4741_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4723l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4741_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4723l) (hubSubn 7 6 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4741_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4723l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4741 :
    hubcapFit theRedpart rf7 p7_4723l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 6 0 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4741_1, c7_4741_2, c7_4741_3, c7_4741_4, c7_4741_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4722l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4722l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4722l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4722l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4742_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4722l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4742 :
    hubcapFit theRedpart rf7 p7_4722l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4742_1, c7_4742_2, c7_4742_3, c7_4742_4, c7_4742_5, c7_4742_6, c7_4742_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4721l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4721l) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4721l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4744_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4721l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4744 :
    hubcapFit theRedpart rf7 p7_4721l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4744_1, c7_4744_2, c7_4744_3, c7_4744_4, c7_4744_5, c7_4744_6, c7_4744_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4749r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4749r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4749r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4749r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4749r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4750_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4749r) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4750 :
    hubcapFit theRedpart rf7 p7_4749r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4750_1, c7_4750_2, c7_4750_3, c7_4750_4, c7_4750_5, c7_4750_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4749l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4749l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4749l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4751_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4751 :
    hubcapFit theRedpart rf7 p7_4749l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4751_1, c7_4751_2, c7_4751_3, c7_4751_4, c7_4751_5, c7_4751_6, c7_4751_7]

end FourColor

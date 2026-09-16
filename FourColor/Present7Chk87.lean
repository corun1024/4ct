import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 87 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4654l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4661_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4654l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4661 :
    hubcapFit theRedpart rf7 p7_4654l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4661_1, c7_4661_2, c7_4661_3, c7_4661_4, c7_4661_5, c7_4661_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4653l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4653l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4653l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4653l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4653l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4663_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4653l) (hubSubn 7 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4663 :
    hubcapFit theRedpart rf7 p7_4653l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 1 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4663_1, c7_4663_2, c7_4663_3, c7_4663_4, c7_4663_5, c7_4663_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4669r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4669r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4670_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4669r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4670 :
    hubcapFit theRedpart rf7 p7_4669r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4670_1, c7_4670_2, c7_4670_3, c7_4670_4, c7_4670_5, c7_4670_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4669l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4669l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4669l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4671_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4669l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4671 :
    hubcapFit theRedpart rf7 p7_4669l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4671_1, c7_4671_2, c7_4671_3, c7_4671_4, c7_4671_5, c7_4671_6, c7_4671_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4668l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4668l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4673_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4668l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4673 :
    hubcapFit theRedpart rf7 p7_4668l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4673_1, c7_4673_2, c7_4673_3, c7_4673_4, c7_4673_5, c7_4673_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4678r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4678r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4679_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4678r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4679 :
    hubcapFit theRedpart rf7 p7_4678r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4679_1, c7_4679_2, c7_4679_3, c7_4679_4, c7_4679_5, c7_4679_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4678l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4678l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4680_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4678l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4680 :
    hubcapFit theRedpart rf7 p7_4678l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4680_1, c7_4680_2, c7_4680_3, c7_4680_4, c7_4680_5, c7_4680_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4677l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4677l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4677l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4682_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4677l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4682 :
    hubcapFit theRedpart rf7 p7_4677l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4682_1, c7_4682_2, c7_4682_3, c7_4682_4, c7_4682_5, c7_4682_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4676l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4676l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4676l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4676l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4676l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4683_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4676l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4683 :
    hubcapFit theRedpart rf7 p7_4676l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4683_1, c7_4683_2, c7_4683_3, c7_4683_4, c7_4683_5, c7_4683_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4675l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4675l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4675l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4675l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4675l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4685_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4675l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4685 :
    hubcapFit theRedpart rf7 p7_4675l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4685_1, c7_4685_2, c7_4685_3, c7_4685_4, c7_4685_5, c7_4685_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4674l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4674l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4674l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4674l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4674l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4686_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4674l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4686 :
    hubcapFit theRedpart rf7 p7_4674l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4686_1, c7_4686_2, c7_4686_3, c7_4686_4, c7_4686_5, c7_4686_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4666l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4666l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4666l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4689_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4666l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4689 :
    hubcapFit theRedpart rf7 p7_4666l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4689_1, c7_4689_2, c7_4689_3, c7_4689_4, c7_4689_5, c7_4689_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4665l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4665l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4690_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4665l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4690 :
    hubcapFit theRedpart rf7 p7_4665l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4690_1, c7_4690_2, c7_4690_3, c7_4690_4, c7_4690_5, c7_4690_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4701r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4701r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4702_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4701r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4702 :
    hubcapFit theRedpart rf7 p7_4701r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4702_1, c7_4702_2, c7_4702_3, c7_4702_4, c7_4702_5, c7_4702_6, c7_4702_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4701l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4701l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4701l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4703_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4701l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4703 :
    hubcapFit theRedpart rf7 p7_4701l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4703_1, c7_4703_2, c7_4703_3, c7_4703_4, c7_4703_5, c7_4703_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4700l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4700l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4705_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4700l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4705 :
    hubcapFit theRedpart rf7 p7_4700l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4705_1, c7_4705_2, c7_4705_3, c7_4705_4, c7_4705_5, c7_4705_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4699l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4699l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4699l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4699l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4699l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4706_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4699l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4706 :
    hubcapFit theRedpart rf7 p7_4699l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4706_1, c7_4706_2, c7_4706_3, c7_4706_4, c7_4706_5, c7_4706_6]

end FourColor

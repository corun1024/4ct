import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 14 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_685l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_685l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_685l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_699_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_685l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_699 :
    hubcapFit theRedpart rf8 p8_685l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_699_1, c8_699_2, c8_699_3, c8_699_4, c8_699_5, c8_699_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_701_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_683l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_701_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_683l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_701_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_683l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_701_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_683l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_701_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_683l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_701 :
    hubcapFit theRedpart rf8 p8_683l
    (Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_701_1, c8_701_2, c8_701_3, c8_701_4, c8_701_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_703_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_662l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_703_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_662l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_703_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_662l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_703_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_662l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_703 :
    hubcapFit theRedpart rf8 p8_662l
    (Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_703_1, c8_703_2, c8_703_3, c8_703_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_709r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_709r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_709r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_709r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_709r) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_710_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_709r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_710 :
    hubcapFit theRedpart rf8 p8_709r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_710_1, c8_710_2, c8_710_3, c8_710_4, c8_710_5, c8_710_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_709l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_709l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_709l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_711_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_709l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_711 :
    hubcapFit theRedpart rf8 p8_709l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_711_1, c8_711_2, c8_711_3, c8_711_4, c8_711_5, c8_711_6, c8_711_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_713_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_713_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_708l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_713_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_708l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_713_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_708l) (hubSubn 8 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_713_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_708l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_713 :
    hubcapFit theRedpart rf8 p8_708l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_713_1, c8_713_2, c8_713_3, c8_713_4, c8_713_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_707l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_707l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_707l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_714_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_707l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_714 :
    hubcapFit theRedpart rf8 p8_707l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_714_1, c8_714_2, c8_714_3, c8_714_4, c8_714_5, c8_714_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_706l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_706l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_706l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_716_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_706l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_716 :
    hubcapFit theRedpart rf8 p8_706l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_716_1, c8_716_2, c8_716_3, c8_716_4, c8_716_5, c8_716_6, c8_716_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_718_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_705l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_718_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_718_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_705l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_718_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_705l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_718_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_705l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_718 :
    hubcapFit theRedpart rf8 p8_705l
    (Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_718_1, c8_718_2, c8_718_3, c8_718_4, c8_718_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_720_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_660l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_720_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_720_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_660l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_720_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_660l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_720_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_660l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_720 :
    hubcapFit theRedpart rf8 p8_660l
    (Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_720_1, c8_720_2, c8_720_3, c8_720_4, c8_720_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_659l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_659l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_659l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_659l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_721_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_659l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_721 :
    hubcapFit theRedpart rf8 p8_659l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_721_1, c8_721_2, c8_721_3, c8_721_4, c8_721_5, c8_721_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_610l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_610l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_610l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_610l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_610l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_723_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_610l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_723 :
    hubcapFit theRedpart rf8 p8_610l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_723_1, c8_723_2, c8_723_3, c8_723_4, c8_723_5, c8_723_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_609l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_609l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_725_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_609l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_725 :
    hubcapFit theRedpart rf8 p8_609l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_725_1, c8_725_2, c8_725_3, c8_725_4, c8_725_5, c8_725_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_608l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_608l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_608l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_608l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_726_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_608l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_726 :
    hubcapFit theRedpart rf8 p8_608l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_726_1, c8_726_2, c8_726_3, c8_726_4, c8_726_5, c8_726_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_607l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_607l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_607l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_607l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_607l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_728_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_607l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_728 :
    hubcapFit theRedpart rf8 p8_607l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_728_1, c8_728_2, c8_728_3, c8_728_4, c8_728_5, c8_728_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_750_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_749r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_750_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_749r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_750_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_749r) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_750_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_749r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_750_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_749r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_750 :
    hubcapFit theRedpart rf8 p8_749r
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_750_1, c8_750_2, c8_750_3, c8_750_4, c8_750_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_751_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_751_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_749l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_751_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_749l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_751_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_749l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_751_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_749l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_751 :
    hubcapFit theRedpart rf8 p8_749l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_751_1, c8_751_2, c8_751_3, c8_751_4, c8_751_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_753_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_748l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_753_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_748l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_753_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_748l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_753_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_748l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_753_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_748l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_753 :
    hubcapFit theRedpart rf8 p8_748l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_753_1, c8_753_2, c8_753_3, c8_753_4, c8_753_5]

end FourColor

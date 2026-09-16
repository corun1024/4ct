import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 31 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1520l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1520l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1520l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1520l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1520l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1520l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1528_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1520l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1528 :
    hubcapFit theRedpart rf8 p8_1520l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1528_1, c8_1528_2, c8_1528_3, c8_1528_4, c8_1528_5, c8_1528_6, c8_1528_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1519l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1519l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1519l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1519l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1519l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1530_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1519l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1530 :
    hubcapFit theRedpart rf8 p8_1519l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1530_1, c8_1530_2, c8_1530_3, c8_1530_4, c8_1530_5, c8_1530_6, c8_1530_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1518l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1518l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1518l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1518l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1518l) (hubSubn 8 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1532_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1518l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1532 :
    hubcapFit theRedpart rf8 p8_1518l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1532_1, c8_1532_2, c8_1532_3, c8_1532_4, c8_1532_5, c8_1532_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1517l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1517l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1517l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1533_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1517l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1533 :
    hubcapFit theRedpart rf8 p8_1517l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1533_1, c8_1533_2, c8_1533_3, c8_1533_4, c8_1533_5, c8_1533_6, c8_1533_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1516l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1516l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1516l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1535_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1516l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1535 :
    hubcapFit theRedpart rf8 p8_1516l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1535_1, c8_1535_2, c8_1535_3, c8_1535_4, c8_1535_5, c8_1535_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1515l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1515l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1515l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1515l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1515l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1515l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1536_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1515l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1536 :
    hubcapFit theRedpart rf8 p8_1515l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1536_1, c8_1536_2, c8_1536_3, c8_1536_4, c8_1536_5, c8_1536_6, c8_1536_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1514l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1514l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1538_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1514l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1538 :
    hubcapFit theRedpart rf8 p8_1514l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1538_1, c8_1538_2, c8_1538_3, c8_1538_4, c8_1538_5, c8_1538_6, c8_1538_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1462l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1462l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1462l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1541_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1462l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1541 :
    hubcapFit theRedpart rf8 p8_1462l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1541_1, c8_1541_2, c8_1541_3, c8_1541_4, c8_1541_5, c8_1541_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1461l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1461l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1461l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1542_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1461l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1542 :
    hubcapFit theRedpart rf8 p8_1461l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1542_1, c8_1542_2, c8_1542_3, c8_1542_4, c8_1542_5, c8_1542_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1356l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1356l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1356l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1356l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1356l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1544_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1356l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1544 :
    hubcapFit theRedpart rf8 p8_1356l
    (Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1544_1, c8_1544_2, c8_1544_3, c8_1544_4, c8_1544_5, c8_1544_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1355l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1355l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1355l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1546_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1355l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1546 :
    hubcapFit theRedpart rf8 p8_1355l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1546_1, c8_1546_2, c8_1546_3, c8_1546_4, c8_1546_5, c8_1546_6, c8_1546_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1354l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1354l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1354l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1354l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1548_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1354l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1548 :
    hubcapFit theRedpart rf8 p8_1354l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1548_1, c8_1548_2, c8_1548_3, c8_1548_4, c8_1548_5, c8_1548_6, c8_1548_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1551_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1176l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1551_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1176l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1551_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1176l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1551_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1176l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1551_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1176l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1551 :
    hubcapFit theRedpart rf8 p8_1176l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1551_1, c8_1551_2, c8_1551_3, c8_1551_4, c8_1551_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1564_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1563l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1564_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1563l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1564_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1563l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1564_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1563l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1564_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1563l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1564 :
    hubcapFit theRedpart rf8 p8_1563l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1564_1, c8_1564_2, c8_1564_3, c8_1564_4, c8_1564_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1566_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1563r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1566_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1563r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1566_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1563r) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1566_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1563r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1566_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1563r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1566 :
    hubcapFit theRedpart rf8 p8_1563r
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1566_1, c8_1566_2, c8_1566_3, c8_1566_4, c8_1566_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1569_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1562r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1569_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1562r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1569_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1562r) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1569_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1562r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1569_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1562r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1569 :
    hubcapFit theRedpart rf8 p8_1562r
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1569_1, c8_1569_2, c8_1569_3, c8_1569_4, c8_1569_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1574_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1573l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1574_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1573l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1574_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1573l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1574_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1573l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1574_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1573l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1574 :
    hubcapFit theRedpart rf8 p8_1573l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1574_1, c8_1574_2, c8_1574_3, c8_1574_4, c8_1574_5]

end FourColor

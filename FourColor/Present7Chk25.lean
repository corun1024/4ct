import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 25 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1371l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1371l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1371l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1371l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1371l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1380_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1371l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1380 :
    hubcapFit theRedpart rf7 p7_1371l
    (Hubcap.one 0 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1380_1, c7_1380_2, c7_1380_3, c7_1380_4, c7_1380_5, c7_1380_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1386_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1385r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1386_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1385r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1386_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1385r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1386_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1385r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1386_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1385r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1386 :
    hubcapFit theRedpart rf7 p7_1385r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1386_1, c7_1386_2, c7_1386_3, c7_1386_4, c7_1386_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1384l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1384l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1384l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1384l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1384l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1387_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1384l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1387 :
    hubcapFit theRedpart rf7 p7_1384l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1387_1, c7_1387_2, c7_1387_3, c7_1387_4, c7_1387_5, c7_1387_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1389r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1389r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1389r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1389r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1389r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1390_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1389r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1390 :
    hubcapFit theRedpart rf7 p7_1389r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1390_1, c7_1390_2, c7_1390_3, c7_1390_4, c7_1390_5, c7_1390_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1391_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1391_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1389l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1391_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1389l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1391_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1389l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1391 :
    hubcapFit theRedpart rf7 p7_1389l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1391_1, c7_1391_2, c7_1391_3, c7_1391_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1382l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1382l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1382l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1382l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1382l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1393_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1382l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1393 :
    hubcapFit theRedpart rf7 p7_1382l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1393_1, c7_1393_2, c7_1393_3, c7_1393_4, c7_1393_5, c7_1393_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1400_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1399r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1400_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1399r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1400_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1399r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1400_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1399r) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1400_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1399r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1400 :
    hubcapFit theRedpart rf7 p7_1399r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1400_1, c7_1400_2, c7_1400_3, c7_1400_4, c7_1400_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1401_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1399l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1401_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1399l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1401_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1399l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1401_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1399l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1401 :
    hubcapFit theRedpart rf7 p7_1399l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1401_1, c7_1401_2, c7_1401_3, c7_1401_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1403_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1398l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1403_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1398l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1403_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1398l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1403_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1398l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1403_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1398l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1403 :
    hubcapFit theRedpart rf7 p7_1398l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1403_1, c7_1403_2, c7_1403_3, c7_1403_4, c7_1403_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1404_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1397l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1404_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1397l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1404_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1397l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1404_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1397l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1404_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1397l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1404 :
    hubcapFit theRedpart rf7 p7_1397l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1404_1, c7_1404_2, c7_1404_3, c7_1404_4, c7_1404_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1408_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1407r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1408_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1407r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1408_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1407r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1408_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1407r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1408_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1407r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1408 :
    hubcapFit theRedpart rf7 p7_1407r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1408_1, c7_1408_2, c7_1408_3, c7_1408_4, c7_1408_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1409_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1407l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1409_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1407l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1409_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1407l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1409_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1407l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1409 :
    hubcapFit theRedpart rf7 p7_1407l
    (Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1409_1, c7_1409_2, c7_1409_3, c7_1409_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1411_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1406l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1411_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1406l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1411_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1406l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1411_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1406l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1411_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1406l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1411 :
    hubcapFit theRedpart rf7 p7_1406l
    (Hubcap.two 0 2 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1411_1, c7_1411_2, c7_1411_3, c7_1411_4, c7_1411_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1417r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1417r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1417r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1417r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1417r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1418_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1417r) (hubSubn 7 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1418 :
    hubcapFit theRedpart rf7 p7_1417r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1418_1, c7_1418_2, c7_1418_3, c7_1418_4, c7_1418_5, c7_1418_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1417l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1417l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1419_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1419 :
    hubcapFit theRedpart rf7 p7_1417l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1419_1, c7_1419_2, c7_1419_3, c7_1419_4, c7_1419_5, c7_1419_6, c7_1419_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1421_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1416l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1421_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1416l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1421_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1421_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1416l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1421_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1416l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1421 :
    hubcapFit theRedpart rf7 p7_1416l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1421_1, c7_1421_2, c7_1421_3, c7_1421_4, c7_1421_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1423_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1423_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1423_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1414l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1423_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1414l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1423_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1414l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1423 :
    hubcapFit theRedpart rf7 p7_1414l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1423_1, c7_1423_2, c7_1423_3, c7_1423_4, c7_1423_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1424_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1424_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1413l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1424_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1413l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1424_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1413l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1424 :
    hubcapFit theRedpart rf7 p7_1413l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1424_1, c7_1424_2, c7_1424_3, c7_1424_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1433r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1433r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1433r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1433r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1433r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1434_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1433r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1434 :
    hubcapFit theRedpart rf7 p7_1433r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1434_1, c7_1434_2, c7_1434_3, c7_1434_4, c7_1434_5, c7_1434_6]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 44 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2075r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2075r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2075r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2075r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2075r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2075r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2075r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2078_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2075r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2078 :
    hubcapFit theRedpart rf9 p9_2075r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2078_1, c9_2078_2, c9_2078_3, c9_2078_4, c9_2078_5, c9_2078_6, c9_2078_7, c9_2078_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2096r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2096r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2096r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2097_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2096r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2097 :
    hubcapFit theRedpart rf9 p9_2096r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2097_1, c9_2097_2, c9_2097_3, c9_2097_4, c9_2097_5, c9_2097_6, c9_2097_7, c9_2097_8, c9_2097_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2090l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2090l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2090l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2090l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2100_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2090l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2100 :
    hubcapFit theRedpart rf9 p9_2090l
    (Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2100_1, c9_2100_2, c9_2100_3, c9_2100_4, c9_2100_5, c9_2100_6, c9_2100_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2089l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2089l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2089l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2089l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2089l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2089l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2102_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2089l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2102 :
    hubcapFit theRedpart rf9 p9_2089l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2102_1, c9_2102_2, c9_2102_3, c9_2102_4, c9_2102_5, c9_2102_6, c9_2102_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2088l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2104_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2088l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2104 :
    hubcapFit theRedpart rf9 p9_2088l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2104_1, c9_2104_2, c9_2104_3, c9_2104_4, c9_2104_5, c9_2104_6, c9_2104_7, c9_2104_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2087l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2087l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2106_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2087l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2106 :
    hubcapFit theRedpart rf9 p9_2087l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2106_1, c9_2106_2, c9_2106_3, c9_2106_4, c9_2106_5, c9_2106_6, c9_2106_7, c9_2106_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2112r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2112r) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2113_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2112r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2113 :
    hubcapFit theRedpart rf9 p9_2112r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2113_1, c9_2113_2, c9_2113_3, c9_2113_4, c9_2113_5, c9_2113_6, c9_2113_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2108l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2108l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2108l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2108l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2108l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2115_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2108l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2115 :
    hubcapFit theRedpart rf9 p9_2108l
    (Hubcap.one 0 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2115_1, c9_2115_2, c9_2115_3, c9_2115_4, c9_2115_5, c9_2115_6, c9_2115_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2121r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2121r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2122_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2122 :
    hubcapFit theRedpart rf9 p9_2121r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2122_1, c9_2122_2, c9_2122_3, c9_2122_4, c9_2122_5, c9_2122_6, c9_2122_7, c9_2122_8, c9_2122_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2121l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2123_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2123 :
    hubcapFit theRedpart rf9 p9_2121l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2123_1, c9_2123_2, c9_2123_3, c9_2123_4, c9_2123_5, c9_2123_6, c9_2123_7, c9_2123_8, c9_2123_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2118l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2118l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2118l) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2125_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2118l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2125 :
    hubcapFit theRedpart rf9 p9_2118l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2125_1, c9_2125_2, c9_2125_3, c9_2125_4, c9_2125_5, c9_2125_6, c9_2125_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2084l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2084l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2127_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2084l) (hubSubn 9 4 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2127 :
    hubcapFit theRedpart rf9 p9_2084l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2127_1, c9_2127_2, c9_2127_3, c9_2127_4, c9_2127_5, c9_2127_6, c9_2127_7, c9_2127_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2129_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2083l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2129 :
    hubcapFit theRedpart rf9 p9_2083l
    (Hubcap.one 0 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2129_1, c9_2129_2, c9_2129_3, c9_2129_4, c9_2129_5, c9_2129_6, c9_2129_7, c9_2129_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2132l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2133_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2132l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2133 :
    hubcapFit theRedpart rf9 p9_2132l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2133_1, c9_2133_2, c9_2133_3, c9_2133_4, c9_2133_5, c9_2133_6, c9_2133_7]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 46 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2167l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2167l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2167l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2167l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2167l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2167l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2167l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2191_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2167l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2191 :
    hubcapFit theRedpart rf9 p9_2167l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2191_1, c9_2191_2, c9_2191_3, c9_2191_4, c9_2191_5, c9_2191_6, c9_2191_7, c9_2191_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2166l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2166l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2193_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2166l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2193 :
    hubcapFit theRedpart rf9 p9_2166l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2193_1, c9_2193_2, c9_2193_3, c9_2193_4, c9_2193_5, c9_2193_6, c9_2193_7, c9_2193_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2195l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2195l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2196_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2195l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2196 :
    hubcapFit theRedpart rf9 p9_2195l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2196_1, c9_2196_2, c9_2196_3, c9_2196_4, c9_2196_5, c9_2196_6, c9_2196_7, c9_2196_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2195r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2195r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2195r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2195r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2198_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2195r) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2198 :
    hubcapFit theRedpart rf9 p9_2195r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2198_1, c9_2198_2, c9_2198_3, c9_2198_4, c9_2198_5, c9_2198_6, c9_2198_7, c9_2198_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2164l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2164l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2164l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2201_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2164l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2201 :
    hubcapFit theRedpart rf9 p9_2164l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2201_1, c9_2201_2, c9_2201_3, c9_2201_4, c9_2201_5, c9_2201_6, c9_2201_7, c9_2201_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2163l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2163l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2163l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2163l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2163l) (hubSubn 9 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2203_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2163l) (hubSubn 9 7 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2203 :
    hubcapFit theRedpart rf9 p9_2163l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 3 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2203_1, c9_2203_2, c9_2203_3, c9_2203_4, c9_2203_5, c9_2203_6, c9_2203_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2205l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2206_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2205l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2206 :
    hubcapFit theRedpart rf9 p9_2205l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2206_1, c9_2206_2, c9_2206_3, c9_2206_4, c9_2206_5, c9_2206_6, c9_2206_7, c9_2206_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2205r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2205r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2205r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2205r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2205r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2205r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2205r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2208_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2205r) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2208 :
    hubcapFit theRedpart rf9 p9_2205r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2208_1, c9_2208_2, c9_2208_3, c9_2208_4, c9_2208_5, c9_2208_6, c9_2208_7, c9_2208_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2161l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2161l) (hubSubn 9 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2211_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2161l) (hubSubn 9 8 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2211 :
    hubcapFit theRedpart rf9 p9_2161l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2211_1, c9_2211_2, c9_2211_3, c9_2211_4, c9_2211_5, c9_2211_6, c9_2211_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2160l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2160l) (hubSubn 9 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2213_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2160l) (hubSubn 9 7 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2213 :
    hubcapFit theRedpart rf9 p9_2160l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 3 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2213_1, c9_2213_2, c9_2213_3, c9_2213_4, c9_2213_5, c9_2213_6, c9_2213_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2227r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2227r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2227r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2227r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2227r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2227r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2227r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2227r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2228_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2227r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2228 :
    hubcapFit theRedpart rf9 p9_2227r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2228_1, c9_2228_2, c9_2228_3, c9_2228_4, c9_2228_5, c9_2228_6, c9_2228_7, c9_2228_8, c9_2228_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2229_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2229 :
    hubcapFit theRedpart rf9 p9_2227l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2229_1, c9_2229_2, c9_2229_3, c9_2229_4, c9_2229_5, c9_2229_6, c9_2229_7, c9_2229_8, c9_2229_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2225l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2225l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2225l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2225l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2225l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2231_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2225l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2231 :
    hubcapFit theRedpart rf9 p9_2225l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2231_1, c9_2231_2, c9_2231_3, c9_2231_4, c9_2231_5, c9_2231_6, c9_2231_7, c9_2231_8, c9_2231_9]

end FourColor

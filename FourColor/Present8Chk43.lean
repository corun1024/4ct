import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 43 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2187l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2187l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2195_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2187l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2195 :
    hubcapFit theRedpart rf8 p8_2187l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2195_1, c8_2195_2, c8_2195_3, c8_2195_4, c8_2195_5, c8_2195_6, c8_2195_7, c8_2195_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2180l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2180l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2180l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2197_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2180l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2197 :
    hubcapFit theRedpart rf8 p8_2180l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2197_1, c8_2197_2, c8_2197_3, c8_2197_4, c8_2197_5, c8_2197_6, c8_2197_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2178l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2178l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2199_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2178l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2199 :
    hubcapFit theRedpart rf8 p8_2178l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2199_1, c8_2199_2, c8_2199_3, c8_2199_4, c8_2199_5, c8_2199_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2176l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2176l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2201_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2176l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2201 :
    hubcapFit theRedpart rf8 p8_2176l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2201_1, c8_2201_2, c8_2201_3, c8_2201_4, c8_2201_5, c8_2201_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2207r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2207r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2207r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2207r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2207r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2207r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2207r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2208_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2207r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2208 :
    hubcapFit theRedpart rf8 p8_2207r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2208_1, c8_2208_2, c8_2208_3, c8_2208_4, c8_2208_5, c8_2208_6, c8_2208_7, c8_2208_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2207l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2207l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2207l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2209_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2207l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2209 :
    hubcapFit theRedpart rf8 p8_2207l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2209_1, c8_2209_2, c8_2209_3, c8_2209_4, c8_2209_5, c8_2209_6, c8_2209_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2206l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2206l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2211_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2206l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2211 :
    hubcapFit theRedpart rf8 p8_2206l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2211_1, c8_2211_2, c8_2211_3, c8_2211_4, c8_2211_5, c8_2211_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2205l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2205l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2205l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2212_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2205l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2212 :
    hubcapFit theRedpart rf8 p8_2205l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2212_1, c8_2212_2, c8_2212_3, c8_2212_4, c8_2212_5, c8_2212_6, c8_2212_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2204l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2204l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2204l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2214_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2204l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2214 :
    hubcapFit theRedpart rf8 p8_2204l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2214_1, c8_2214_2, c8_2214_3, c8_2214_4, c8_2214_5, c8_2214_6, c8_2214_7, c8_2214_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2203l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2216_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2216 :
    hubcapFit theRedpart rf8 p8_2203l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2216_1, c8_2216_2, c8_2216_3, c8_2216_4, c8_2216_5, c8_2216_6, c8_2216_7, c8_2216_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2174l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2174l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2218_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2174l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2218 :
    hubcapFit theRedpart rf8 p8_2174l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2218_1, c8_2218_2, c8_2218_3, c8_2218_4, c8_2218_5, c8_2218_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2173l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2173l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2220_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2173l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2220 :
    hubcapFit theRedpart rf8 p8_2173l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2220_1, c8_2220_2, c8_2220_3, c8_2220_4, c8_2220_5, c8_2220_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2172l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2172l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2172l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2221_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2172l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2221 :
    hubcapFit theRedpart rf8 p8_2172l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2221_1, c8_2221_2, c8_2221_3, c8_2221_4, c8_2221_5, c8_2221_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2171l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2171l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2171l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2223_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2223 :
    hubcapFit theRedpart rf8 p8_2171l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2223_1, c8_2223_2, c8_2223_3, c8_2223_4, c8_2223_5, c8_2223_6, c8_2223_7, c8_2223_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2245r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2245r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2245r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2245r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2245r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2246_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2245r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2246 :
    hubcapFit theRedpart rf8 p8_2245r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2246_1, c8_2246_2, c8_2246_3, c8_2246_4, c8_2246_5, c8_2246_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2245l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2247_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2245l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2247 :
    hubcapFit theRedpart rf8 p8_2245l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2247_1, c8_2247_2, c8_2247_3, c8_2247_4, c8_2247_5, c8_2247_6]

end FourColor

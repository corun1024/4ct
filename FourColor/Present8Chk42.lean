import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 42 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2149r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2149r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2149r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2149r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2149r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2149r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2150_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2149r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2150 :
    hubcapFit theRedpart rf8 p8_2149r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2150_1, c8_2150_2, c8_2150_3, c8_2150_4, c8_2150_5, c8_2150_6, c8_2150_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2149l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2149l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2149l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2151_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2149l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2151 :
    hubcapFit theRedpart rf8 p8_2149l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2151_1, c8_2151_2, c8_2151_3, c8_2151_4, c8_2151_5, c8_2151_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2153_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2153_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2153_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2148l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2153_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2148l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2153_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2148l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2153 :
    hubcapFit theRedpart rf8 p8_2148l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2153_1, c8_2153_2, c8_2153_3, c8_2153_4, c8_2153_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2147l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2154_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2147l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2154 :
    hubcapFit theRedpart rf8 p8_2147l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2154_1, c8_2154_2, c8_2154_3, c8_2154_4, c8_2154_5, c8_2154_6, c8_2154_7, c8_2154_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2146l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2156_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2146l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2156 :
    hubcapFit theRedpart rf8 p8_2146l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2156_1, c8_2156_2, c8_2156_3, c8_2156_4, c8_2156_5, c8_2156_6, c8_2156_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2127l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2127l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2127l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2159_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2127l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2159 :
    hubcapFit theRedpart rf8 p8_2127l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2159_1, c8_2159_2, c8_2159_3, c8_2159_4, c8_2159_5, c8_2159_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2160_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2126l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2160_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2126l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2160_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2126l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2160_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2126l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2160_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2126l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2160 :
    hubcapFit theRedpart rf8 p8_2126l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2160_1, c8_2160_2, c8_2160_3, c8_2160_4, c8_2160_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2162_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2125l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2162_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2125l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2162_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2125l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2162_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2125l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2162_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2125l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2162 :
    hubcapFit theRedpart rf8 p8_2125l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2162_1, c8_2162_2, c8_2162_3, c8_2162_4, c8_2162_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2163_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2124l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2163_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2163_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2124l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2163_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2124l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2163_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2124l) (hubSubn 8 7 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2163 :
    hubcapFit theRedpart rf8 p8_2124l
    (Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2163_1, c8_2163_2, c8_2163_3, c8_2163_4, c8_2163_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2166_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2165r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2166_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2166_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2165r) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2166_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2165r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2166_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2165r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2166 :
    hubcapFit theRedpart rf8 p8_2165r
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2166_1, c8_2166_2, c8_2166_3, c8_2166_4, c8_2166_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2167_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2165l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2167_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2167_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2165l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2167_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2165l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2167_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2165l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2167 :
    hubcapFit theRedpart rf8 p8_2165l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2167_1, c8_2167_2, c8_2167_3, c8_2167_4, c8_2167_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2052l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2052l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2052l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2170_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2052l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2170 :
    hubcapFit theRedpart rf8 p8_2052l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2170_1, c8_2170_2, c8_2170_3, c8_2170_4, c8_2170_5, c8_2170_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2183r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2183r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2183r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2183r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2183r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2184_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2183r) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2184 :
    hubcapFit theRedpart rf8 p8_2183r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2184_1, c8_2184_2, c8_2184_3, c8_2184_4, c8_2184_5, c8_2184_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2183l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2183l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2183l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2185_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2183l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2185 :
    hubcapFit theRedpart rf8 p8_2183l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2185_1, c8_2185_2, c8_2185_3, c8_2185_4, c8_2185_5, c8_2185_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2189r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2189r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2189r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2189r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2189r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2189r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2190_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2189r) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2190 :
    hubcapFit theRedpart rf8 p8_2189r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2190_1, c8_2190_2, c8_2190_3, c8_2190_4, c8_2190_5, c8_2190_6, c8_2190_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2189l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2189l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2189l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2191_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2189l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2191 :
    hubcapFit theRedpart rf8 p8_2189l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2191_1, c8_2191_2, c8_2191_3, c8_2191_4, c8_2191_5, c8_2191_6, c8_2191_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2188l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2193_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2188l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2193 :
    hubcapFit theRedpart rf8 p8_2188l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2193_1, c8_2193_2, c8_2193_3, c8_2193_4, c8_2193_5, c8_2193_6, c8_2193_7]

end FourColor

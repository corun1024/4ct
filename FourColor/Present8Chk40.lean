import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 40 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2038_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2006l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2038 :
    hubcapFit theRedpart rf8 p8_2006l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2038_1, c8_2038_2, c8_2038_3, c8_2038_4, c8_2038_5, c8_2038_6, c8_2038_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1949l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1949l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1949l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2040_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1949l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2040 :
    hubcapFit theRedpart rf8 p8_1949l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2040_1, c8_2040_2, c8_2040_3, c8_2040_4, c8_2040_5, c8_2040_6, c8_2040_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1913l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2043_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1913l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2043 :
    hubcapFit theRedpart rf8 p8_1913l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2043_1, c8_2043_2, c8_2043_3, c8_2043_4, c8_2043_5, c8_2043_6, c8_2043_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2045_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1912l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2045 :
    hubcapFit theRedpart rf8 p8_1912l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2045_1, c8_2045_2, c8_2045_3, c8_2045_4, c8_2045_5, c8_2045_6, c8_2045_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2063r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2063r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2063r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2063r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2063r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2064_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2063r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2064 :
    hubcapFit theRedpart rf8 p8_2063r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2064_1, c8_2064_2, c8_2064_3, c8_2064_4, c8_2064_5, c8_2064_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2063l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2065_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2063l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2065 :
    hubcapFit theRedpart rf8 p8_2063l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2065_1, c8_2065_2, c8_2065_3, c8_2065_4, c8_2065_5, c8_2065_6, c8_2065_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2067_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2067_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2061l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2067_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2061l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2067_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2061l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2067_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2061l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2067 :
    hubcapFit theRedpart rf8 p8_2061l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2067_1, c8_2067_2, c8_2067_3, c8_2067_4, c8_2067_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2060l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2060l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2060l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2069_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2060l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2069 :
    hubcapFit theRedpart rf8 p8_2060l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2069_1, c8_2069_2, c8_2069_3, c8_2069_4, c8_2069_5, c8_2069_6, c8_2069_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2072r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2072r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2072r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2072r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2072r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2072r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2073_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2072r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2073 :
    hubcapFit theRedpart rf8 p8_2072r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2073_1, c8_2073_2, c8_2073_3, c8_2073_4, c8_2073_5, c8_2073_6, c8_2073_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2072l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2072l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2074_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2072l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2074 :
    hubcapFit theRedpart rf8 p8_2072l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2074_1, c8_2074_2, c8_2074_3, c8_2074_4, c8_2074_5, c8_2074_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2076_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2071l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2076_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2071l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2076_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2071l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2076_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2071l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2076_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2071l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2076 :
    hubcapFit theRedpart rf8 p8_2071l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2076_1, c8_2076_2, c8_2076_3, c8_2076_4, c8_2076_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2090r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2090r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2090r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2090r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2090r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2090r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2091_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2090r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2091 :
    hubcapFit theRedpart rf8 p8_2090r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2091_1, c8_2091_2, c8_2091_3, c8_2091_4, c8_2091_5, c8_2091_6, c8_2091_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2090l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2090l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2090l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2092_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2090l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2092 :
    hubcapFit theRedpart rf8 p8_2090l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2092_1, c8_2092_2, c8_2092_3, c8_2092_4, c8_2092_5, c8_2092_6, c8_2092_7, c8_2092_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2089l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2089l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2089l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2094_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2089l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2094 :
    hubcapFit theRedpart rf8 p8_2089l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2094_1, c8_2094_2, c8_2094_3, c8_2094_4, c8_2094_5, c8_2094_6, c8_2094_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2087l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2087l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2087l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2096_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2096 :
    hubcapFit theRedpart rf8 p8_2087l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2096_1, c8_2096_2, c8_2096_3, c8_2096_4, c8_2096_5, c8_2096_6, c8_2096_7, c8_2096_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2101r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2101r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2101r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2101r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2101r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2101r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2101r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2102_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2101r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2102 :
    hubcapFit theRedpart rf8 p8_2101r
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2102_1, c8_2102_2, c8_2102_3, c8_2102_4, c8_2102_5, c8_2102_6, c8_2102_7, c8_2102_8]

end FourColor

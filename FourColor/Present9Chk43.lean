import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 43 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2035r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2035r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2035r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2035r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2035r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2035r) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2036_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2035r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2036 :
    hubcapFit theRedpart rf9 p9_2035r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2036_1, c9_2036_2, c9_2036_3, c9_2036_4, c9_2036_5, c9_2036_6, c9_2036_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2035l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2035l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2035l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2035l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2035l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2035l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2035l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2035l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2037_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2035l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2037 :
    hubcapFit theRedpart rf9 p9_2035l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2037_1, c9_2037_2, c9_2037_3, c9_2037_4, c9_2037_5, c9_2037_6, c9_2037_7, c9_2037_8, c9_2037_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2033l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2033l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2039_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2033l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2039 :
    hubcapFit theRedpart rf9 p9_2033l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2039_1, c9_2039_2, c9_2039_3, c9_2039_4, c9_2039_5, c9_2039_6, c9_2039_7, c9_2039_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2029l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2029l) (hubSubn 9 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2041_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2029l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2041 :
    hubcapFit theRedpart rf9 p9_2029l
    (Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2041_1, c9_2041_2, c9_2041_3, c9_2041_4, c9_2041_5, c9_2041_6, c9_2041_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2028l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2028l) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2043_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2028l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2043 :
    hubcapFit theRedpart rf9 p9_2028l
    (Hubcap.one 0 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2043_1, c9_2043_2, c9_2043_3, c9_2043_4, c9_2043_5, c9_2043_6, c9_2043_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2019l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2019l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2046_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2019l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2046 :
    hubcapFit theRedpart rf9 p9_2019l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2046_1, c9_2046_2, c9_2046_3, c9_2046_4, c9_2046_5, c9_2046_6, c9_2046_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2018l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2018l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2048_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2018l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2048 :
    hubcapFit theRedpart rf9 p9_2018l
    (Hubcap.one 0 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2048_1, c9_2048_2, c9_2048_3, c9_2048_4, c9_2048_5, c9_2048_6, c9_2048_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1953l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1953l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1953l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2051_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1953l) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2051 :
    hubcapFit theRedpart rf9 p9_1953l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2051_1, c9_2051_2, c9_2051_3, c9_2051_4, c9_2051_5, c9_2051_6, c9_2051_7, c9_2051_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2059r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2059r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2059r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2059r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2059r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2059r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2059r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2060_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2059r) (hubSubn 9 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2060 :
    hubcapFit theRedpart rf9 p9_2059r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2060_1, c9_2060_2, c9_2060_3, c9_2060_4, c9_2060_5, c9_2060_6, c9_2060_7, c9_2060_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2061l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2061l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2061l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2061l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2061l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2061l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2062_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2061l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2062 :
    hubcapFit theRedpart rf9 p9_2061l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2062_1, c9_2062_2, c9_2062_3, c9_2062_4, c9_2062_5, c9_2062_6, c9_2062_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2064l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2065_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2064l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2065 :
    hubcapFit theRedpart rf9 p9_2064l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2065_1, c9_2065_2, c9_2065_3, c9_2065_4, c9_2065_5, c9_2065_6, c9_2065_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2064r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2064r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2064r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2064r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2064r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2064r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2067_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2064r) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2067 :
    hubcapFit theRedpart rf9 p9_2064r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2067_1, c9_2067_2, c9_2067_3, c9_2067_4, c9_2067_5, c9_2067_6, c9_2067_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2072l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2073_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2072l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2073 :
    hubcapFit theRedpart rf9 p9_2072l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2073_1, c9_2073_2, c9_2073_3, c9_2073_4, c9_2073_5, c9_2073_6, c9_2073_7, c9_2073_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2075l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2075l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2075l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2075l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2075l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2075l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2075l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2076_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2075l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2076 :
    hubcapFit theRedpart rf9 p9_2075l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2076_1, c9_2076_2, c9_2076_3, c9_2076_4, c9_2076_5, c9_2076_6, c9_2076_7, c9_2076_8]

end FourColor

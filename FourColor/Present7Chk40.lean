import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 40 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2200_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2200_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2188l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2200_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2188l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2200_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2188l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2200_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2188l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2200 :
    hubcapFit theRedpart rf7 p7_2188l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2200_1, c7_2200_2, c7_2200_3, c7_2200_4, c7_2200_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2207r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2207r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2207r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2207r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2207r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2208_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2207r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2208 :
    hubcapFit theRedpart rf7 p7_2207r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2208_1, c7_2208_2, c7_2208_3, c7_2208_4, c7_2208_5, c7_2208_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2209_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2209_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2207l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2209_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2209_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2207l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2209_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2207l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2209 :
    hubcapFit theRedpart rf7 p7_2207l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2209_1, c7_2209_2, c7_2209_3, c7_2209_4, c7_2209_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2206l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2211_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2211 :
    hubcapFit theRedpart rf7 p7_2206l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2211_1, c7_2211_2, c7_2211_3, c7_2211_4, c7_2211_5, c7_2211_6, c7_2211_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2213_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2204l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2213_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2204l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2213_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2204l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2213_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2204l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2213 :
    hubcapFit theRedpart rf7 p7_2204l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2213_1, c7_2213_2, c7_2213_3, c7_2213_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2215_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2215_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2203l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2215_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2203l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2215_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2203l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2215_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2203l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2215 :
    hubcapFit theRedpart rf7 p7_2203l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2215_1, c7_2215_2, c7_2215_3, c7_2215_4, c7_2215_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2224r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2224r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2224r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2224r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2224r) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2224r) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2225_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2224r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2225 :
    hubcapFit theRedpart rf7 p7_2224r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2225_1, c7_2225_2, c7_2225_3, c7_2225_4, c7_2225_5, c7_2225_6, c7_2225_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2226_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2224l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2226_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2224l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2226_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2224l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2226_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2224l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2226_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2224l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2226 :
    hubcapFit theRedpart rf7 p7_2224l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2226_1, c7_2226_2, c7_2226_3, c7_2226_4, c7_2226_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2221l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2221l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2221l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2221l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2221l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2228_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2221l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2228 :
    hubcapFit theRedpart rf7 p7_2221l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2228_1, c7_2228_2, c7_2228_3, c7_2228_4, c7_2228_5, c7_2228_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2233r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2233r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2233r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2233r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2233r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2234_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2233r) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2234 :
    hubcapFit theRedpart rf7 p7_2233r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2234_1, c7_2234_2, c7_2234_3, c7_2234_4, c7_2234_5, c7_2234_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2232l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2232l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2232l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2232l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2232l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2236_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2232l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2236 :
    hubcapFit theRedpart rf7 p7_2232l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2236_1, c7_2236_2, c7_2236_3, c7_2236_4, c7_2236_5, c7_2236_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2231l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2231l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2231l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2231l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2231l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2237_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2237 :
    hubcapFit theRedpart rf7 p7_2231l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2237_1, c7_2237_2, c7_2237_3, c7_2237_4, c7_2237_5, c7_2237_6, c7_2237_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2239_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2239_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2230l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2239_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2230l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2239_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2230l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2239_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2230l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2239 :
    hubcapFit theRedpart rf7 p7_2230l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2239_1, c7_2239_2, c7_2239_3, c7_2239_4, c7_2239_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2252r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2252r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2252r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2252r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2252r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2253_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2252r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2253 :
    hubcapFit theRedpart rf7 p7_2252r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2253_1, c7_2253_2, c7_2253_3, c7_2253_4, c7_2253_5, c7_2253_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2252l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2252l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2252l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2252l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2252l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2254_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2252l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2254 :
    hubcapFit theRedpart rf7 p7_2252l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2254_1, c7_2254_2, c7_2254_3, c7_2254_4, c7_2254_5, c7_2254_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2251l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2251l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2251l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2256_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2251l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2256 :
    hubcapFit theRedpart rf7 p7_2251l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2256_1, c7_2256_2, c7_2256_3, c7_2256_4, c7_2256_5, c7_2256_6, c7_2256_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2250l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2250l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2250l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2250l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2250l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2258_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2250l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2258 :
    hubcapFit theRedpart rf7 p7_2250l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2258_1, c7_2258_2, c7_2258_3, c7_2258_4, c7_2258_5, c7_2258_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2249l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2259_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2249l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2259 :
    hubcapFit theRedpart rf7 p7_2249l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2259_1, c7_2259_2, c7_2259_3, c7_2259_4, c7_2259_5, c7_2259_6]

end FourColor

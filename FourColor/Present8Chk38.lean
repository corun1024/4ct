import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 38 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1938r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1938r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1938r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1938r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1938r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1939_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1938r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1939 :
    hubcapFit theRedpart rf8 p8_1938r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1939_1, c8_1939_2, c8_1939_3, c8_1939_4, c8_1939_5, c8_1939_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1940_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1938l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1940 :
    hubcapFit theRedpart rf8 p8_1938l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1940_1, c8_1940_2, c8_1940_3, c8_1940_4, c8_1940_5, c8_1940_6, c8_1940_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1921l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1921l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1921l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1921l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1921l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1942_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1921l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1942 :
    hubcapFit theRedpart rf8 p8_1921l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1942_1, c8_1942_2, c8_1942_3, c8_1942_4, c8_1942_5, c8_1942_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1920l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1920l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1944_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1920l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1944 :
    hubcapFit theRedpart rf8 p8_1920l
    (Hubcap.one 0 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1944_1, c8_1944_2, c8_1944_3, c8_1944_4, c8_1944_5, c8_1944_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1919l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1945_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1919l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1945 :
    hubcapFit theRedpart rf8 p8_1919l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1945_1, c8_1945_2, c8_1945_3, c8_1945_4, c8_1945_5, c8_1945_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1947_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1918l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1947 :
    hubcapFit theRedpart rf8 p8_1918l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1947_1, c8_1947_2, c8_1947_3, c8_1947_4, c8_1947_5, c8_1947_6, c8_1947_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1963r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1963r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1963r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1963r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1963r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1964_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1963r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1964 :
    hubcapFit theRedpart rf8 p8_1963r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1964_1, c8_1964_2, c8_1964_3, c8_1964_4, c8_1964_5, c8_1964_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1963l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1963l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1965_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1963l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1965 :
    hubcapFit theRedpart rf8 p8_1963l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1965_1, c8_1965_2, c8_1965_3, c8_1965_4, c8_1965_5, c8_1965_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1978r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1978r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1978r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1978r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1978r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1979_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1978r) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1979 :
    hubcapFit theRedpart rf8 p8_1978r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1979_1, c8_1979_2, c8_1979_3, c8_1979_4, c8_1979_5, c8_1979_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1978l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1978l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1978l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1978l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1980_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1978l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1980 :
    hubcapFit theRedpart rf8 p8_1978l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1980_1, c8_1980_2, c8_1980_3, c8_1980_4, c8_1980_5, c8_1980_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1977l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1977l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1977l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1977l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1977l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1982_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1977l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1982 :
    hubcapFit theRedpart rf8 p8_1977l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1982_1, c8_1982_2, c8_1982_3, c8_1982_4, c8_1982_5, c8_1982_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1974l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1974l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1974l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1974l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1974l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1974l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1984_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1974l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1984 :
    hubcapFit theRedpart rf8 p8_1974l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1984_1, c8_1984_2, c8_1984_3, c8_1984_4, c8_1984_5, c8_1984_6, c8_1984_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1973l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1973l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1973l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1973l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1973l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1986_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1973l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1986 :
    hubcapFit theRedpart rf8 p8_1973l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1986_1, c8_1986_2, c8_1986_3, c8_1986_4, c8_1986_5, c8_1986_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1988_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1988_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1988_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1970l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1988_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1970l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1988_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1970l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1988 :
    hubcapFit theRedpart rf8 p8_1970l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1988_1, c8_1988_2, c8_1988_3, c8_1988_4, c8_1988_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1969l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1969l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1969l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1990_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1969l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1990 :
    hubcapFit theRedpart rf8 p8_1969l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1990_1, c8_1990_2, c8_1990_3, c8_1990_4, c8_1990_5, c8_1990_6, c8_1990_7, c8_1990_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1967l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1967l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1967l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1992_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1967l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1992 :
    hubcapFit theRedpart rf8 p8_1967l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1992_1, c8_1992_2, c8_1992_3, c8_1992_4, c8_1992_5, c8_1992_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1994_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1994_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1994_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1959l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1994_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1959l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1994_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1959l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1994 :
    hubcapFit theRedpart rf8 p8_1959l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1994_1, c8_1994_2, c8_1994_3, c8_1994_4, c8_1994_5]

end FourColor

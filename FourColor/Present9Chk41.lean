import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 41 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1919l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1932_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1919l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1932 :
    hubcapFit theRedpart rf9 p9_1919l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1932_1, c9_1932_2, c9_1932_3, c9_1932_4, c9_1932_5, c9_1932_6, c9_1932_7, c9_1932_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1934l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1935_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1934l) (hubSubn 9 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1935 :
    hubcapFit theRedpart rf9 p9_1934l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1935_1, c9_1935_2, c9_1935_3, c9_1935_4, c9_1935_5, c9_1935_6, c9_1935_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1937l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1937l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1938_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1937l) (hubSubn 9 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1938 :
    hubcapFit theRedpart rf9 p9_1937l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1938_1, c9_1938_2, c9_1938_3, c9_1938_4, c9_1938_5, c9_1938_6, c9_1938_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1937r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1937r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1937r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1937r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1937r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1937r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1940_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1937r) (hubSubn 9 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1940 :
    hubcapFit theRedpart rf9 p9_1937r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1940_1, c9_1940_2, c9_1940_3, c9_1940_4, c9_1940_5, c9_1940_6, c9_1940_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1878l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1878l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1878l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1944_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1878l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1944 :
    hubcapFit theRedpart rf9 p9_1878l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1944_1, c9_1944_2, c9_1944_3, c9_1944_4, c9_1944_5, c9_1944_6, c9_1944_7, c9_1944_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1877l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1877l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1877l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1877l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1877l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1946_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1877l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1946 :
    hubcapFit theRedpart rf9 p9_1877l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1946_1, c9_1946_2, c9_1946_3, c9_1946_4, c9_1946_5, c9_1946_6, c9_1946_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1876l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1876l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1876l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1876l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1948_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1876l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1948 :
    hubcapFit theRedpart rf9 p9_1876l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1948_1, c9_1948_2, c9_1948_3, c9_1948_4, c9_1948_5, c9_1948_6, c9_1948_7, c9_1948_8, c9_1948_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1971r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1972_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1971r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1972 :
    hubcapFit theRedpart rf9 p9_1971r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1972_1, c9_1972_2, c9_1972_3, c9_1972_4, c9_1972_5, c9_1972_6, c9_1972_7, c9_1972_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1971l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1973_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1973 :
    hubcapFit theRedpart rf9 p9_1971l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1973_1, c9_1973_2, c9_1973_3, c9_1973_4, c9_1973_5, c9_1973_6, c9_1973_7, c9_1973_8, c9_1973_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1970l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1975_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1970l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1975 :
    hubcapFit theRedpart rf9 p9_1970l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1975_1, c9_1975_2, c9_1975_3, c9_1975_4, c9_1975_5, c9_1975_6, c9_1975_7, c9_1975_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1968l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1968l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1968l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1977_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1968l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1977 :
    hubcapFit theRedpart rf9 p9_1968l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1977_1, c9_1977_2, c9_1977_3, c9_1977_4, c9_1977_5, c9_1977_6, c9_1977_7, c9_1977_8, c9_1977_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1967l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1967l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1979_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1967l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1979 :
    hubcapFit theRedpart rf9 p9_1967l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1979_1, c9_1979_2, c9_1979_3, c9_1979_4, c9_1979_5, c9_1979_6, c9_1979_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1966l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1966l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1966l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1966l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1981_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1981 :
    hubcapFit theRedpart rf9 p9_1966l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1981_1, c9_1981_2, c9_1981_3, c9_1981_4, c9_1981_5, c9_1981_6, c9_1981_7, c9_1981_8, c9_1981_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1964l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1964l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1983_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1964l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1983 :
    hubcapFit theRedpart rf9 p9_1964l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1983_1, c9_1983_2, c9_1983_3, c9_1983_4, c9_1983_5, c9_1983_6, c9_1983_7, c9_1983_8]

end FourColor

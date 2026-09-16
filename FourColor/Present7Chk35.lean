import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 35 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1919l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1924_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1919l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1924 :
    hubcapFit theRedpart rf7 p7_1919l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1924_1, c7_1924_2, c7_1924_3, c7_1924_4, c7_1924_5, c7_1924_6, c7_1924_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1917l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1917l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1917l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1917l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1917l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1926_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1917l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1926 :
    hubcapFit theRedpart rf7 p7_1917l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1926_1, c7_1926_2, c7_1926_3, c7_1926_4, c7_1926_5, c7_1926_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1932r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1932r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1932r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1932r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1932r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1933_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1932r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1933 :
    hubcapFit theRedpart rf7 p7_1932r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1933_1, c7_1933_2, c7_1933_3, c7_1933_4, c7_1933_5, c7_1933_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1931l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1931l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1931l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1931l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1934_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1934 :
    hubcapFit theRedpart rf7 p7_1931l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1934_1, c7_1934_2, c7_1934_3, c7_1934_4, c7_1934_5, c7_1934_6, c7_1934_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1929l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1929l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1929l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1936_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1929l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1936 :
    hubcapFit theRedpart rf7 p7_1929l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1936_1, c7_1936_2, c7_1936_3, c7_1936_4, c7_1936_5, c7_1936_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1949r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1949r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1949r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1949r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1949r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1950_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1949r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1950 :
    hubcapFit theRedpart rf7 p7_1949r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1950_1, c7_1950_2, c7_1950_3, c7_1950_4, c7_1950_5, c7_1950_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1949l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1949l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1949l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1949l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1949l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1951_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1949l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1951 :
    hubcapFit theRedpart rf7 p7_1949l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1951_1, c7_1951_2, c7_1951_3, c7_1951_4, c7_1951_5, c7_1951_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1948l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1948l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1948l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1948l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1948l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1953_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1948l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1953 :
    hubcapFit theRedpart rf7 p7_1948l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1953_1, c7_1953_2, c7_1953_3, c7_1953_4, c7_1953_5, c7_1953_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1947l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1947l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1947l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1947l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1947l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1947l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1954_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1947l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1954 :
    hubcapFit theRedpart rf7 p7_1947l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1954_1, c7_1954_2, c7_1954_3, c7_1954_4, c7_1954_5, c7_1954_6, c7_1954_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1946l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1946l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1946l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1946l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1946l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1946l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1956_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1946l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1956 :
    hubcapFit theRedpart rf7 p7_1946l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1956_1, c7_1956_2, c7_1956_3, c7_1956_4, c7_1956_5, c7_1956_6, c7_1956_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1945l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1945l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1945l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1945l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1945l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1945l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1958_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1945l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1958 :
    hubcapFit theRedpart rf7 p7_1945l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1958_1, c7_1958_2, c7_1958_3, c7_1958_4, c7_1958_5, c7_1958_6, c7_1958_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1944l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1944l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1944l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1944l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1944l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1960_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1944l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1960 :
    hubcapFit theRedpart rf7 p7_1944l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1960_1, c7_1960_2, c7_1960_3, c7_1960_4, c7_1960_5, c7_1960_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1942l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1942l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1942l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1942l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1942l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1962_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1942l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1962 :
    hubcapFit theRedpart rf7 p7_1942l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1962_1, c7_1962_2, c7_1962_3, c7_1962_4, c7_1962_5, c7_1962_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1966r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1966r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1966r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1966r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1966r) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1967_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1966r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1967 :
    hubcapFit theRedpart rf7 p7_1966r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1967_1, c7_1967_2, c7_1967_3, c7_1967_4, c7_1967_5, c7_1967_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1966l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1966l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1966l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1966l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1966l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1966l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1968_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1966l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1968 :
    hubcapFit theRedpart rf7 p7_1966l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1968_1, c7_1968_2, c7_1968_3, c7_1968_4, c7_1968_5, c7_1968_6, c7_1968_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1964l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1964l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1964l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1964l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1964l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1970_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1964l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1970 :
    hubcapFit theRedpart rf7 p7_1964l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1970_1, c7_1970_2, c7_1970_3, c7_1970_4, c7_1970_5, c7_1970_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1974r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1974r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1974r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1974r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1974r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1975_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1974r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1975 :
    hubcapFit theRedpart rf7 p7_1974r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1975_1, c7_1975_2, c7_1975_3, c7_1975_4, c7_1975_5, c7_1975_6]

end FourColor

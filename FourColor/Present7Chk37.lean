import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 37 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2031_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2030r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2031_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2030r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2031_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2030r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2031_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2030r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2031_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2030r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2031 :
    hubcapFit theRedpart rf7 p7_2030r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2031_1, c7_2031_2, c7_2031_3, c7_2031_4, c7_2031_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2030l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2030l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2030l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2032_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2030l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2032 :
    hubcapFit theRedpart rf7 p7_2030l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2032_1, c7_2032_2, c7_2032_3, c7_2032_4, c7_2032_5, c7_2032_6, c7_2032_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2034_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2034_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2034_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2028l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2034_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2028l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2034_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2028l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2034 :
    hubcapFit theRedpart rf7 p7_2028l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2034_1, c7_2034_2, c7_2034_3, c7_2034_4, c7_2034_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2049r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2049r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2049r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2049r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2049r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2050_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2049r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2050 :
    hubcapFit theRedpart rf7 p7_2049r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2050_1, c7_2050_2, c7_2050_3, c7_2050_4, c7_2050_5, c7_2050_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2052_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2047l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2052 :
    hubcapFit theRedpart rf7 p7_2047l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2052_1, c7_2052_2, c7_2052_3, c7_2052_4, c7_2052_5, c7_2052_6, c7_2052_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2044l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2044l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2044l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2044l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2044l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2054_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2044l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2054 :
    hubcapFit theRedpart rf7 p7_2044l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2054_1, c7_2054_2, c7_2054_3, c7_2054_4, c7_2054_5, c7_2054_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2058r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2058r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2058r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2058r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2058r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2059_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2058r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2059 :
    hubcapFit theRedpart rf7 p7_2058r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2059_1, c7_2059_2, c7_2059_3, c7_2059_4, c7_2059_5, c7_2059_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2060_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2058l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2060_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2058l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2060_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2058l) (hubSubn 7 5 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2060_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2058l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2060 :
    hubcapFit theRedpart rf7 p7_2058l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2060_1, c7_2060_2, c7_2060_3, c7_2060_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2062_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2057l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2062_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2057l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2062_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2057l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2062_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2057l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2062 :
    hubcapFit theRedpart rf7 p7_2057l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2062_1, c7_2062_2, c7_2062_3, c7_2062_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2070r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2070r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2070r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2070r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2070r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2070r) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2071_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2070r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2071 :
    hubcapFit theRedpart rf7 p7_2070r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2071_1, c7_2071_2, c7_2071_3, c7_2071_4, c7_2071_5, c7_2071_6, c7_2071_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2072_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2070l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2072_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2070l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2072_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2070l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2072_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2070l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2072_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2070l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2072 :
    hubcapFit theRedpart rf7 p7_2070l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2072_1, c7_2072_2, c7_2072_3, c7_2072_4, c7_2072_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2067l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2067l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2067l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2067l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2067l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2074_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2067l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2074 :
    hubcapFit theRedpart rf7 p7_2067l
    (Hubcap.one 1 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2074_1, c7_2074_2, c7_2074_3, c7_2074_4, c7_2074_5, c7_2074_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2077r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2077r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2077r) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2077r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2077r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2078_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2077r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2078 :
    hubcapFit theRedpart rf7 p7_2077r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2078_1, c7_2078_2, c7_2078_3, c7_2078_4, c7_2078_5, c7_2078_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2079_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2079_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2077l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2079_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2079_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2077l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2079_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2077l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2079 :
    hubcapFit theRedpart rf7 p7_2077l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2079_1, c7_2079_2, c7_2079_3, c7_2079_4, c7_2079_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2081_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2076l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2081_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2076l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2081_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2076l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2081_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2076l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2081 :
    hubcapFit theRedpart rf7 p7_2076l
    (Hubcap.one 1 1 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2081_1, c7_2081_2, c7_2081_3, c7_2081_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2083_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2065l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2083_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2065l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2083_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2065l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2083_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2065l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2083_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2065l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2083 :
    hubcapFit theRedpart rf7 p7_2065l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2083_1, c7_2083_2, c7_2083_3, c7_2083_4, c7_2083_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2086r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2087_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2086r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2087 :
    hubcapFit theRedpart rf7 p7_2086r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2087_1, c7_2087_2, c7_2087_3, c7_2087_4, c7_2087_5, c7_2087_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2088_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2086l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2088_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2088_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2088_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2086l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2088_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2086l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2088 :
    hubcapFit theRedpart rf7 p7_2086l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2088_1, c7_2088_2, c7_2088_3, c7_2088_4, c7_2088_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2090_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2085l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2090_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2085l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2090_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2085l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2090_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2085l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2090_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2085l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2090 :
    hubcapFit theRedpart rf7 p7_2085l
    (Hubcap.one 1 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2090_1, c7_2090_2, c7_2090_3, c7_2090_4, c7_2090_5]

end FourColor

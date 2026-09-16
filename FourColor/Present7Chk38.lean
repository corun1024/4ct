import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 38 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2094r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2094r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2094r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2094r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2094r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2095_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2094r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2095 :
    hubcapFit theRedpart rf7 p7_2094r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2095_1, c7_2095_2, c7_2095_3, c7_2095_4, c7_2095_5, c7_2095_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2094l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2094l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2094l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2094l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2094l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2096_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2094l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2096 :
    hubcapFit theRedpart rf7 p7_2094l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2096_1, c7_2096_2, c7_2096_3, c7_2096_4, c7_2096_5, c7_2096_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2093l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2093l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2093l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2093l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2098_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2093l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2098 :
    hubcapFit theRedpart rf7 p7_2093l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2098_1, c7_2098_2, c7_2098_3, c7_2098_4, c7_2098_5, c7_2098_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2099_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2099_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2092l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2099_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2092l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2099_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2092l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2099_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2092l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2099 :
    hubcapFit theRedpart rf7 p7_2092l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2099_1, c7_2099_2, c7_2099_3, c7_2099_4, c7_2099_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2112_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2111r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2112_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2111r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2112_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2111r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2112_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2111r) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2112_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2111r) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2112 :
    hubcapFit theRedpart rf7 p7_2111r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2112_1, c7_2112_2, c7_2112_3, c7_2112_4, c7_2112_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2111l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2111l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2111l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2111l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2111l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2113_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2111l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2113 :
    hubcapFit theRedpart rf7 p7_2111l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2113_1, c7_2113_2, c7_2113_3, c7_2113_4, c7_2113_5, c7_2113_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2119r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2119r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2120_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2119r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2120 :
    hubcapFit theRedpart rf7 p7_2119r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2120_1, c7_2120_2, c7_2120_3, c7_2120_4, c7_2120_5, c7_2120_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2119l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2119l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2119l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2119l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2119l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2121_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2119l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2121 :
    hubcapFit theRedpart rf7 p7_2119l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2121_1, c7_2121_2, c7_2121_3, c7_2121_4, c7_2121_5, c7_2121_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2118l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2118l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2123_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2118l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2123 :
    hubcapFit theRedpart rf7 p7_2118l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2123_1, c7_2123_2, c7_2123_3, c7_2123_4, c7_2123_5, c7_2123_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2117l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2117l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2117l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2117l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2124_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2124 :
    hubcapFit theRedpart rf7 p7_2117l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2124_1, c7_2124_2, c7_2124_3, c7_2124_4, c7_2124_5, c7_2124_6, c7_2124_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2116l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2116l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2116l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2116l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2116l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2116l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2126_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2116l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2126 :
    hubcapFit theRedpart rf7 p7_2116l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2126_1, c7_2126_2, c7_2126_3, c7_2126_4, c7_2126_5, c7_2126_6, c7_2126_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2115l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2115l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2115l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2128_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2115l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2128 :
    hubcapFit theRedpart rf7 p7_2115l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2128_1, c7_2128_2, c7_2128_3, c7_2128_4, c7_2128_5, c7_2128_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2108l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2108l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2108l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2108l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2108l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2130_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2108l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2130 :
    hubcapFit theRedpart rf7 p7_2108l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2130_1, c7_2130_2, c7_2130_3, c7_2130_4, c7_2130_5, c7_2130_6, c7_2130_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2135r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2135r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2135r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2135r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2135r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2136_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2135r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2136 :
    hubcapFit theRedpart rf7 p7_2135r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2136_1, c7_2136_2, c7_2136_3, c7_2136_4, c7_2136_5, c7_2136_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2137_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2135l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2137_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2135l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2137_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2135l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2137_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2135l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2137_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2135l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2137 :
    hubcapFit theRedpart rf7 p7_2135l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2137_1, c7_2137_2, c7_2137_3, c7_2137_4, c7_2137_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2134l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2134l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2134l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2134l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2139_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2134l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2139 :
    hubcapFit theRedpart rf7 p7_2134l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2139_1, c7_2139_2, c7_2139_3, c7_2139_4, c7_2139_5, c7_2139_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2141_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2132l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2141_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2132l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2141_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2132l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2141_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2132l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2141 :
    hubcapFit theRedpart rf7 p7_2132l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2141_1, c7_2141_2, c7_2141_3, c7_2141_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2147r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2147r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2147r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2147r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2147r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2148_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2147r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2148 :
    hubcapFit theRedpart rf7 p7_2147r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2148_1, c7_2148_2, c7_2148_3, c7_2148_4, c7_2148_5, c7_2148_6]

end FourColor

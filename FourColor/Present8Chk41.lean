import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 41 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2101l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2101l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2101l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2101l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2101l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2103_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2101l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2103 :
    hubcapFit theRedpart rf8 p8_2101l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2103_1, c8_2103_2, c8_2103_3, c8_2103_4, c8_2103_5, c8_2103_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2100l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2105_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2100l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2105 :
    hubcapFit theRedpart rf8 p8_2100l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2105_1, c8_2105_2, c8_2105_3, c8_2105_4, c8_2105_5, c8_2105_6, c8_2105_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2098l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2098l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2098l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2098l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2098l) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2107_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2098l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2107 :
    hubcapFit theRedpart rf8 p8_2098l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2107_1, c8_2107_2, c8_2107_3, c8_2107_4, c8_2107_5, c8_2107_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2084l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2084l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2084l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2084l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2084l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2109_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2084l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2109 :
    hubcapFit theRedpart rf8 p8_2084l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2109_1, c8_2109_2, c8_2109_3, c8_2109_4, c8_2109_5, c8_2109_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2083l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2111_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2083l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2111 :
    hubcapFit theRedpart rf8 p8_2083l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2111_1, c8_2111_2, c8_2111_3, c8_2111_4, c8_2111_5, c8_2111_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2113_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2113_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2113_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2081l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2113_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2081l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2113_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2081l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2113 :
    hubcapFit theRedpart rf8 p8_2081l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2113_1, c8_2113_2, c8_2113_3, c8_2113_4, c8_2113_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2080l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2114_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2080l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2114 :
    hubcapFit theRedpart rf8 p8_2080l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2114_1, c8_2114_2, c8_2114_3, c8_2114_4, c8_2114_5, c8_2114_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2079l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2079l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2116_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2079l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2116 :
    hubcapFit theRedpart rf8 p8_2079l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2116_1, c8_2116_2, c8_2116_3, c8_2116_4, c8_2116_5, c8_2116_6, c8_2116_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2078l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2078l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2078l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2078l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2078l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2118_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2078l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2118 :
    hubcapFit theRedpart rf8 p8_2078l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2118_1, c8_2118_2, c8_2118_3, c8_2118_4, c8_2118_5, c8_2118_6, c8_2118_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2120_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2055l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2120_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2120_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2055l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2120_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2055l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2120_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2055l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2120 :
    hubcapFit theRedpart rf8 p8_2055l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2120_1, c8_2120_2, c8_2120_3, c8_2120_4, c8_2120_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2122_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2054l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2122_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2122_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2054l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2122_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2054l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2122_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2054l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2122 :
    hubcapFit theRedpart rf8 p8_2054l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2122_1, c8_2122_2, c8_2122_3, c8_2122_4, c8_2122_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2135r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2135r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2135r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2135r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2135r) (hubSubn 8 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2136_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2135r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2136 :
    hubcapFit theRedpart rf8 p8_2135r
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2136_1, c8_2136_2, c8_2136_3, c8_2136_4, c8_2136_5, c8_2136_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2135l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2135l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2135l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2135l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2135l) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2137_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2135l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2137 :
    hubcapFit theRedpart rf8 p8_2135l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2137_1, c8_2137_2, c8_2137_3, c8_2137_4, c8_2137_5, c8_2137_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2134l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2134l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2134l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2134l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2134l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2139_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2139 :
    hubcapFit theRedpart rf8 p8_2134l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2139_1, c8_2139_2, c8_2139_3, c8_2139_4, c8_2139_5, c8_2139_6, c8_2139_7, c8_2139_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2141_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2133l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2141_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2141_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2133l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2141_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2133l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2141_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2133l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2141 :
    hubcapFit theRedpart rf8 p8_2133l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2141_1, c8_2141_2, c8_2141_3, c8_2141_4, c8_2141_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2131l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2131l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2131l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2131l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2131l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2143_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2131l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2143 :
    hubcapFit theRedpart rf8 p8_2131l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2143_1, c8_2143_2, c8_2143_3, c8_2143_4, c8_2143_5, c8_2143_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2129l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2129l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2129l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2129l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2145_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2129l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2145 :
    hubcapFit theRedpart rf8 p8_2129l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2145_1, c8_2145_2, c8_2145_3, c8_2145_4, c8_2145_5, c8_2145_6]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 45 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2137l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2138_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2137l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2138 :
    hubcapFit theRedpart rf9 p9_2137l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2138_1, c9_2138_2, c9_2138_3, c9_2138_4, c9_2138_5, c9_2138_6, c9_2138_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2137r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2137r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2137r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2137r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2137r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2137r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2140_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2137r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2140 :
    hubcapFit theRedpart rf9 p9_2137r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2140_1, c9_2140_2, c9_2140_3, c9_2140_4, c9_2140_5, c9_2140_6, c9_2140_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2143l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2143l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2144_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2143l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2144 :
    hubcapFit theRedpart rf9 p9_2143l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2144_1, c9_2144_2, c9_2144_3, c9_2144_4, c9_2144_5, c9_2144_6, c9_2144_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2143r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2143r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2143r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2143r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2143r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2143r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2146_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2143r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2146 :
    hubcapFit theRedpart rf9 p9_2143r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2146_1, c9_2146_2, c9_2146_3, c9_2146_4, c9_2146_5, c9_2146_6, c9_2146_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2135r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2135r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2135r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2135r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2135r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2135r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2150_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2135r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2150 :
    hubcapFit theRedpart rf9 p9_2135r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2150_1, c9_2150_2, c9_2150_3, c9_2150_4, c9_2150_5, c9_2150_6, c9_2150_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2131r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2131r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2131r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2131r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2131r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2131r) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2154_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2131r) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2154 :
    hubcapFit theRedpart rf9 p9_2131r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2154_1, c9_2154_2, c9_2154_3, c9_2154_4, c9_2154_5, c9_2154_6, c9_2154_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2175r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2175r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2175r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2175r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2176_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2175r) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2176 :
    hubcapFit theRedpart rf9 p9_2175r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2176_1, c9_2176_2, c9_2176_3, c9_2176_4, c9_2176_5, c9_2176_6, c9_2176_7, c9_2176_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2177_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2175l) (hubSubn 9 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2177 :
    hubcapFit theRedpart rf9 p9_2175l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2177_1, c9_2177_2, c9_2177_3, c9_2177_4, c9_2177_5, c9_2177_6, c9_2177_7, c9_2177_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2174l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2179_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2174l) (hubSubn 9 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2179 :
    hubcapFit theRedpart rf9 p9_2174l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2179_1, c9_2179_2, c9_2179_3, c9_2179_4, c9_2179_5, c9_2179_6, c9_2179_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2173l) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2181_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2173l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2181 :
    hubcapFit theRedpart rf9 p9_2173l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2181_1, c9_2181_2, c9_2181_3, c9_2181_4, c9_2181_5, c9_2181_6, c9_2181_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2172l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2183_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2183 :
    hubcapFit theRedpart rf9 p9_2172l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2183_1, c9_2183_2, c9_2183_3, c9_2183_4, c9_2183_5, c9_2183_6, c9_2183_7, c9_2183_8, c9_2183_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2171l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2185_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2171l) (hubSubn 9 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2185 :
    hubcapFit theRedpart rf9 p9_2171l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2185_1, c9_2185_2, c9_2185_3, c9_2185_4, c9_2185_5, c9_2185_6, c9_2185_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2170l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2187_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2170l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2187 :
    hubcapFit theRedpart rf9 p9_2170l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2187_1, c9_2187_2, c9_2187_3, c9_2187_4, c9_2187_5, c9_2187_6, c9_2187_7, c9_2187_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2168l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2168l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2189_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2168l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2189 :
    hubcapFit theRedpart rf9 p9_2168l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2189_1, c9_2189_2, c9_2189_3, c9_2189_4, c9_2189_5, c9_2189_6, c9_2189_7, c9_2189_8]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 41 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2261_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2248l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2261_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2248l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2261_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2248l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2261_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2248l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2261_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2248l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2261 :
    hubcapFit theRedpart rf7 p7_2248l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 1 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2261_1, c7_2261_2, c7_2261_3, c7_2261_4, c7_2261_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2246l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2246l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2246l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2246l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2263_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2246l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2263 :
    hubcapFit theRedpart rf7 p7_2246l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2263_1, c7_2263_2, c7_2263_3, c7_2263_4, c7_2263_5, c7_2263_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2264_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2245l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2264_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2245l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2264_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2245l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2264_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2245l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2264_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2245l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2264 :
    hubcapFit theRedpart rf7 p7_2245l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2264_1, c7_2264_2, c7_2264_3, c7_2264_4, c7_2264_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2244l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2244l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2244l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2266_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2244l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2266 :
    hubcapFit theRedpart rf7 p7_2244l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2266_1, c7_2266_2, c7_2266_3, c7_2266_4, c7_2266_5, c7_2266_6, c7_2266_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2268_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2268_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2243l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2268_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2243l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2268_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2243l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2268_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2243l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2268 :
    hubcapFit theRedpart rf7 p7_2243l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2268_1, c7_2268_2, c7_2268_3, c7_2268_4, c7_2268_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2269_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2242l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2269_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2269_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2269_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2242l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2269_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2242l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2269 :
    hubcapFit theRedpart rf7 p7_2242l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2269_1, c7_2269_2, c7_2269_3, c7_2269_4, c7_2269_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2271_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2241l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2271_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2241l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2271_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2241l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2271_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2241l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2271_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2241l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2271 :
    hubcapFit theRedpart rf7 p7_2241l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2271_1, c7_2271_2, c7_2271_3, c7_2271_4, c7_2271_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2287_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2286r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2287_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2286r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2287_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2286r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2287_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2286r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2287_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2286r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2287 :
    hubcapFit theRedpart rf7 p7_2286r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2287_1, c7_2287_2, c7_2287_3, c7_2287_4, c7_2287_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2286l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2286l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2286l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2288_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2286l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2288 :
    hubcapFit theRedpart rf7 p7_2286l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2288_1, c7_2288_2, c7_2288_3, c7_2288_4, c7_2288_5, c7_2288_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2285l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2285l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2285l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2285l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2285l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2290_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2285l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2290 :
    hubcapFit theRedpart rf7 p7_2285l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2290_1, c7_2290_2, c7_2290_3, c7_2290_4, c7_2290_5, c7_2290_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2292_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2292_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2283l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2292_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2283l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2292_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2283l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2292_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2283l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2292 :
    hubcapFit theRedpart rf7 p7_2283l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2292_1, c7_2292_2, c7_2292_3, c7_2292_4, c7_2292_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2301_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2300r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2301_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2300r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2301_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2300r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2301_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2300r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2301_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2300r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2301 :
    hubcapFit theRedpart rf7 p7_2300r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2301_1, c7_2301_2, c7_2301_3, c7_2301_4, c7_2301_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2303_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2298l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2303_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2298l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2303_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2298l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2303_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2298l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2303 :
    hubcapFit theRedpart rf7 p7_2298l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2303_1, c7_2303_2, c7_2303_3, c7_2303_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2304_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2297l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2304_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2297l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2304_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2297l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2304_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2297l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2304_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2297l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2304 :
    hubcapFit theRedpart rf7 p7_2297l
    (Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2304_1, c7_2304_2, c7_2304_3, c7_2304_4, c7_2304_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2309_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2308r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2309_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2308r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2309_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2308r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2309_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2308r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2309_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2308r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2309 :
    hubcapFit theRedpart rf7 p7_2308r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2309_1, c7_2309_2, c7_2309_3, c7_2309_4, c7_2309_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2308l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2308l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2308l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2308l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2310_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2308l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2310 :
    hubcapFit theRedpart rf7 p7_2308l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2310_1, c7_2310_2, c7_2310_3, c7_2310_4, c7_2310_5, c7_2310_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2312_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2312_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2307l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2312_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2307l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2312_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2307l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2312_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2307l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2312 :
    hubcapFit theRedpart rf7 p7_2307l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2312_1, c7_2312_2, c7_2312_3, c7_2312_4, c7_2312_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2313_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2306l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2313_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2306l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2313_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2306l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2313_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2306l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2313_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2306l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2313 :
    hubcapFit theRedpart rf7 p7_2306l
    (Hubcap.two 0 3 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2313_1, c7_2313_2, c7_2313_3, c7_2313_4, c7_2313_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2315_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2295l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2315_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2295l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2315_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2295l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2315_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2295l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2315 :
    hubcapFit theRedpart rf7 p7_2295l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2315_1, c7_2315_2, c7_2315_3, c7_2315_4]

end FourColor

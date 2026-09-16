import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 39 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2149_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2149_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2147l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2149_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2147l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2149_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2147l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2149_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2147l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2149 :
    hubcapFit theRedpart rf7 p7_2147l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2149_1, c7_2149_2, c7_2149_3, c7_2149_4, c7_2149_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2151r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2151r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2151r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2151r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2151r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2152_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2151r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2152 :
    hubcapFit theRedpart rf7 p7_2151r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2152_1, c7_2152_2, c7_2152_3, c7_2152_4, c7_2152_5, c7_2152_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2151l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2151l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2151l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2153_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2151l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2153 :
    hubcapFit theRedpart rf7 p7_2151l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2153_1, c7_2153_2, c7_2153_3, c7_2153_4, c7_2153_5, c7_2153_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2155_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2155_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2143l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2155_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2143l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2155_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2143l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2155_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2143l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2155 :
    hubcapFit theRedpart rf7 p7_2143l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2155_1, c7_2155_2, c7_2155_3, c7_2155_4, c7_2155_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2163r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2163r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2163r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2163r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2163r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2164_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2163r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2164 :
    hubcapFit theRedpart rf7 p7_2163r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2164_1, c7_2164_2, c7_2164_3, c7_2164_4, c7_2164_5, c7_2164_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2165_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2165_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2163l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2165_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2163l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2165_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2163l) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2165_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2163l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2165 :
    hubcapFit theRedpart rf7 p7_2163l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2165_1, c7_2165_2, c7_2165_3, c7_2165_4, c7_2165_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2161l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2161l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2161l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2161l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2167_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2161l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2167 :
    hubcapFit theRedpart rf7 p7_2161l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2167_1, c7_2167_2, c7_2167_3, c7_2167_4, c7_2167_5, c7_2167_6, c7_2167_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2176r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2176r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2176r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2176r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2176r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2177_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2176r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2177 :
    hubcapFit theRedpart rf7 p7_2176r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2177_1, c7_2177_2, c7_2177_3, c7_2177_4, c7_2177_5, c7_2177_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2176l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2176l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2176l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2178_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2176l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2178 :
    hubcapFit theRedpart rf7 p7_2176l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2178_1, c7_2178_2, c7_2178_3, c7_2178_4, c7_2178_5, c7_2178_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2175l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2175l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2175l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2180_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2180 :
    hubcapFit theRedpart rf7 p7_2175l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2180_1, c7_2180_2, c7_2180_3, c7_2180_4, c7_2180_5, c7_2180_6, c7_2180_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2173l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2173l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2173l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2173l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2173l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2182_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2182 :
    hubcapFit theRedpart rf7 p7_2173l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2182_1, c7_2182_2, c7_2182_3, c7_2182_4, c7_2182_5, c7_2182_6, c7_2182_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2170l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2170l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2170l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2184_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2170l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2184 :
    hubcapFit theRedpart rf7 p7_2170l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2184_1, c7_2184_2, c7_2184_3, c7_2184_4, c7_2184_5, c7_2184_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2186_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2169l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2186_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2169l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2186_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2169l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2186_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2169l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2186_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2169l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2186 :
    hubcapFit theRedpart rf7 p7_2169l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 5 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2186_1, c7_2186_2, c7_2186_3, c7_2186_4, c7_2186_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2192r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2192r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2192r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2192r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2192r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2193_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2192r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2193 :
    hubcapFit theRedpart rf7 p7_2192r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2193_1, c7_2193_2, c7_2193_3, c7_2193_4, c7_2193_5, c7_2193_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2194_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2192l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2194_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2192l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2194_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2192l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2194_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2192l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2194_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2192l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2194 :
    hubcapFit theRedpart rf7 p7_2192l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2194_1, c7_2194_2, c7_2194_3, c7_2194_4, c7_2194_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2191l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2191l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2191l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2191l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2191l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2196_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2191l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2196 :
    hubcapFit theRedpart rf7 p7_2191l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2196_1, c7_2196_2, c7_2196_3, c7_2196_4, c7_2196_5, c7_2196_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2197_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2190l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2197_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2190l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2197_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2190l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2197_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2190l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2197_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2190l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2197 :
    hubcapFit theRedpart rf7 p7_2190l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2197_1, c7_2197_2, c7_2197_3, c7_2197_4, c7_2197_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2189l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2189l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2189l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2199_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2189l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2199 :
    hubcapFit theRedpart rf7 p7_2189l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2199_1, c7_2199_2, c7_2199_3, c7_2199_4, c7_2199_5, c7_2199_6]

end FourColor

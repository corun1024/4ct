import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 47 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2223l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2223l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2223l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2223l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2233_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2223l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2233 :
    hubcapFit theRedpart rf9 p9_2223l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2233_1, c9_2233_2, c9_2233_3, c9_2233_4, c9_2233_5, c9_2233_6, c9_2233_7, c9_2233_8, c9_2233_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2222l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2222l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2222l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2222l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2222l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2222l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2222l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2235_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2222l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2235 :
    hubcapFit theRedpart rf9 p9_2222l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2235_1, c9_2235_2, c9_2235_3, c9_2235_4, c9_2235_5, c9_2235_6, c9_2235_7, c9_2235_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2221l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2221l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2221l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2221l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2221l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2221l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2221l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2237_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2221l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2237 :
    hubcapFit theRedpart rf9 p9_2221l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2237_1, c9_2237_2, c9_2237_3, c9_2237_4, c9_2237_5, c9_2237_6, c9_2237_7, c9_2237_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2240r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2240r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2241_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2240r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2241 :
    hubcapFit theRedpart rf9 p9_2240r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2241_1, c9_2241_2, c9_2241_3, c9_2241_4, c9_2241_5, c9_2241_6, c9_2241_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2240l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2240l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2240l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2242_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2240l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2242 :
    hubcapFit theRedpart rf9 p9_2240l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2242_1, c9_2242_2, c9_2242_3, c9_2242_4, c9_2242_5, c9_2242_6, c9_2242_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2239l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2239l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2239l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2244_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2239l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2244 :
    hubcapFit theRedpart rf9 p9_2239l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2244_1, c9_2244_2, c9_2244_3, c9_2244_4, c9_2244_5, c9_2244_6, c9_2244_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2218l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2218l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2218l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2218l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2218l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2218l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2218l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2218l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2246_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2218l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2246 :
    hubcapFit theRedpart rf9 p9_2218l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2246_1, c9_2246_2, c9_2246_3, c9_2246_4, c9_2246_5, c9_2246_6, c9_2246_7, c9_2246_8, c9_2246_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2217l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2217l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2248_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2248 :
    hubcapFit theRedpart rf9 p9_2217l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2248_1, c9_2248_2, c9_2248_3, c9_2248_4, c9_2248_5, c9_2248_6, c9_2248_7, c9_2248_8, c9_2248_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2216l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2250_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2216l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2250 :
    hubcapFit theRedpart rf9 p9_2216l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2250_1, c9_2250_2, c9_2250_3, c9_2250_4, c9_2250_5, c9_2250_6, c9_2250_7, c9_2250_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2215l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2215l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2252_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2215l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2252 :
    hubcapFit theRedpart rf9 p9_2215l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2252_1, c9_2252_2, c9_2252_3, c9_2252_4, c9_2252_5, c9_2252_6, c9_2252_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2254l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2254l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2254l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2254l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2254l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2254l) (hubSubn 9 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2255_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2254l) (hubSubn 9 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2255 :
    hubcapFit theRedpart rf9 p9_2254l
    (Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2255_1, c9_2255_2, c9_2255_3, c9_2255_4, c9_2255_5, c9_2255_6, c9_2255_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2254r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2254r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2254r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2254r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2254r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2254r) (hubSubn 9 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2257_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2254r) (hubSubn 9 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2257 :
    hubcapFit theRedpart rf9 p9_2254r
    (Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2257_1, c9_2257_2, c9_2257_3, c9_2257_4, c9_2257_5, c9_2257_6, c9_2257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2272r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2272r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2272r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2273_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2272r) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2273 :
    hubcapFit theRedpart rf9 p9_2272r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2273_1, c9_2273_2, c9_2273_3, c9_2273_4, c9_2273_5, c9_2273_6, c9_2273_7, c9_2273_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2272l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2272l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2274_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2274 :
    hubcapFit theRedpart rf9 p9_2272l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2274_1, c9_2274_2, c9_2274_3, c9_2274_4, c9_2274_5, c9_2274_6, c9_2274_7, c9_2274_8, c9_2274_9]

end FourColor

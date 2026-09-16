import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 63 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2903l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2903l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2903l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2903l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2903l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2903l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2903l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2988_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2903l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2988 :
    hubcapFit theRedpart rf9 p9_2903l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2988_1, c9_2988_2, c9_2988_3, c9_2988_4, c9_2988_5, c9_2988_6, c9_2988_7, c9_2988_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2902l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2902l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2902l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2902l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2902l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2902l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2902l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2902l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2990_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2902l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2990 :
    hubcapFit theRedpart rf9 p9_2902l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2990_1, c9_2990_2, c9_2990_3, c9_2990_4, c9_2990_5, c9_2990_6, c9_2990_7, c9_2990_8, c9_2990_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3010r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3010r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3010r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3010r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3010r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3010r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3011_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3010r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3011 :
    hubcapFit theRedpart rf9 p9_3010r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3011_1, c9_3011_2, c9_3011_3, c9_3011_4, c9_3011_5, c9_3011_6, c9_3011_7, c9_3011_8, c9_3011_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3010l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3010l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3010l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3010l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3010l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3012_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3010l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3012 :
    hubcapFit theRedpart rf9 p9_3010l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3012_1, c9_3012_2, c9_3012_3, c9_3012_4, c9_3012_5, c9_3012_6, c9_3012_7, c9_3012_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3008l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3008l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3008l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3008l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3008l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3008l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3014_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3008l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3014 :
    hubcapFit theRedpart rf9 p9_3008l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3014_1, c9_3014_2, c9_3014_3, c9_3014_4, c9_3014_5, c9_3014_6, c9_3014_7, c9_3014_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3007l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3007l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3007l) (hubSubn 9 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3016_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3007l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3016 :
    hubcapFit theRedpart rf9 p9_3007l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3016_1, c9_3016_2, c9_3016_3, c9_3016_4, c9_3016_5, c9_3016_6, c9_3016_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3006l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3006l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3006l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3018_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3018 :
    hubcapFit theRedpart rf9 p9_3006l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3018_1, c9_3018_2, c9_3018_3, c9_3018_4, c9_3018_5, c9_3018_6, c9_3018_7, c9_3018_8, c9_3018_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3004l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3004l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3004l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3004l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3004l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3004l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3004l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3020_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3004l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3020 :
    hubcapFit theRedpart rf9 p9_3004l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3020_1, c9_3020_2, c9_3020_3, c9_3020_4, c9_3020_5, c9_3020_6, c9_3020_7, c9_3020_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3003l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3003l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3003l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3003l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3003l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3003l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3022_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3022 :
    hubcapFit theRedpart rf9 p9_3003l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3022_1, c9_3022_2, c9_3022_3, c9_3022_4, c9_3022_5, c9_3022_6, c9_3022_7, c9_3022_8, c9_3022_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3030r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3030r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3030r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3030r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3030r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3030r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3030r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3030r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3031_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3030r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3031 :
    hubcapFit theRedpart rf9 p9_3030r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3031_1, c9_3031_2, c9_3031_3, c9_3031_4, c9_3031_5, c9_3031_6, c9_3031_7, c9_3031_8, c9_3031_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3032_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3030l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3032 :
    hubcapFit theRedpart rf9 p9_3030l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3032_1, c9_3032_2, c9_3032_3, c9_3032_4, c9_3032_5, c9_3032_6, c9_3032_7, c9_3032_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3028l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3028l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3028l) (hubSubn 9 8 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3034_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3028l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3034 :
    hubcapFit theRedpart rf9 p9_3028l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 8 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3034_1, c9_3034_2, c9_3034_3, c9_3034_4, c9_3034_5, c9_3034_6, c9_3034_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3027l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3027l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3027l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3027l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3036_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3027l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3036 :
    hubcapFit theRedpart rf9 p9_3027l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3036_1, c9_3036_2, c9_3036_3, c9_3036_4, c9_3036_5, c9_3036_6, c9_3036_7, c9_3036_8]

end FourColor

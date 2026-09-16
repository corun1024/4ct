import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 20 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_846l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_846l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_846l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_915_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_846l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_915 :
    hubcapFit theRedpart rf10 p10_846l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_915_1, c10_915_2, c10_915_3, c10_915_4, c10_915_5, c10_915_6, c10_915_7, c10_915_8, c10_915_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_845l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_845l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_845l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_917_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_917 :
    hubcapFit theRedpart rf10 p10_845l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_917_1, c10_917_2, c10_917_3, c10_917_4, c10_917_5, c10_917_6, c10_917_7, c10_917_8, c10_917_9, c10_917_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_921r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_921r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_921r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_922_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_921r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_922 :
    hubcapFit theRedpart rf10 p10_921r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_922_1, c10_922_2, c10_922_3, c10_922_4, c10_922_5, c10_922_6, c10_922_7, c10_922_8, c10_922_9, c10_922_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_920l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_920l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_924_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_920l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_924 :
    hubcapFit theRedpart rf10 p10_920l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_924_1, c10_924_2, c10_924_3, c10_924_4, c10_924_5, c10_924_6, c10_924_7, c10_924_8, c10_924_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_919l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_919l) (hubSubn 10 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_926_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_919l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_926 :
    hubcapFit theRedpart rf10 p10_919l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_926_1, c10_926_2, c10_926_3, c10_926_4, c10_926_5, c10_926_6, c10_926_7, c10_926_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_938r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_938r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_938r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_938r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_938r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_938r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_938r) (hubSubn 10 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_939_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_938r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_939 :
    hubcapFit theRedpart rf10 p10_938r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_939_1, c10_939_2, c10_939_3, c10_939_4, c10_939_5, c10_939_6, c10_939_7, c10_939_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_938l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_938l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_938l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_940_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_938l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_940 :
    hubcapFit theRedpart rf10 p10_938l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_940_1, c10_940_2, c10_940_3, c10_940_4, c10_940_5, c10_940_6, c10_940_7, c10_940_8, c10_940_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_937l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_937l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_937l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_937l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_942_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_942 :
    hubcapFit theRedpart rf10 p10_937l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_942_1, c10_942_2, c10_942_3, c10_942_4, c10_942_5, c10_942_6, c10_942_7, c10_942_8, c10_942_9, c10_942_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_936l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_944_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_944 :
    hubcapFit theRedpart rf10 p10_936l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_944_1, c10_944_2, c10_944_3, c10_944_4, c10_944_5, c10_944_6, c10_944_7, c10_944_8, c10_944_9, c10_944_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_935l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_935l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_935l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_935l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_935l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_935l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_935l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_935l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_935l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_946_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_935l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_946 :
    hubcapFit theRedpart rf10 p10_935l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_946_1, c10_946_2, c10_946_3, c10_946_4, c10_946_5, c10_946_6, c10_946_7, c10_946_8, c10_946_9, c10_946_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_934l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_934l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_934l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_934l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_948_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_934l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_948 :
    hubcapFit theRedpart rf10 p10_934l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_948_1, c10_948_2, c10_948_3, c10_948_4, c10_948_5, c10_948_6, c10_948_7, c10_948_8, c10_948_9, c10_948_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_932l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_932l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_932l) (hubSubn 10 5 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_932l) (hubSubn 10 6 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_951_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_932l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_951 :
    hubcapFit theRedpart rf10 p10_932l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 8 <|
     Hubcap.two 1 6 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_951_1, c10_951_2, c10_951_3, c10_951_4, c10_951_5, c10_951_6, c10_951_7]

end FourColor

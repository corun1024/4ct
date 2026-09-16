import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 16 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_867_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_840l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_867_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_840l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_867_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_840l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_867_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_840l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_867_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_840l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_867 :
    hubcapFit theRedpart rf7 p7_840l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_867_1, c7_867_2, c7_867_3, c7_867_4, c7_867_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_839l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_839l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_869_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_839l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_869 :
    hubcapFit theRedpart rf7 p7_839l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_869_1, c7_869_2, c7_869_3, c7_869_4, c7_869_5, c7_869_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_838l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_838l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_870_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_838l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_870 :
    hubcapFit theRedpart rf7 p7_838l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_870_1, c7_870_2, c7_870_3, c7_870_4, c7_870_5, c7_870_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_872_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_872_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_872_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_872_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_315l) (hubSubn 7 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_872_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_315l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_872 :
    hubcapFit theRedpart rf7 p7_315l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_872_1, c7_872_2, c7_872_3, c7_872_4, c7_872_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_901r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_901r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_901r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_901r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_901r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_902_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_901r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_902 :
    hubcapFit theRedpart rf7 p7_901r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_902_1, c7_902_2, c7_902_3, c7_902_4, c7_902_5, c7_902_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_901l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_901l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_901l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_901l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_901l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_901l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_903_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_901l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_903 :
    hubcapFit theRedpart rf7 p7_901l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_903_1, c7_903_2, c7_903_3, c7_903_4, c7_903_5, c7_903_6, c7_903_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_898l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_898l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_898l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_898l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_898l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_905_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_898l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_905 :
    hubcapFit theRedpart rf7 p7_898l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_905_1, c7_905_2, c7_905_3, c7_905_4, c7_905_5, c7_905_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_907_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_895l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_907_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_895l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_907_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_895l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_907_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_895l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_907_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_895l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_907 :
    hubcapFit theRedpart rf7 p7_895l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_907_1, c7_907_2, c7_907_3, c7_907_4, c7_907_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_913r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_913r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_913r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_913r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_913r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_914_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_913r) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_914 :
    hubcapFit theRedpart rf7 p7_913r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_914_1, c7_914_2, c7_914_3, c7_914_4, c7_914_5, c7_914_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_915_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_915_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_913l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_915_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_913l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_915_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_913l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_915_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_913l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_915 :
    hubcapFit theRedpart rf7 p7_913l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_915_1, c7_915_2, c7_915_3, c7_915_4, c7_915_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_917_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_917_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_917_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_917_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_912l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_917_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_912l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_917 :
    hubcapFit theRedpart rf7 p7_912l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_917_1, c7_917_2, c7_917_3, c7_917_4, c7_917_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_929r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_929r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_929r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_929r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_929r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_930_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_929r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_930 :
    hubcapFit theRedpart rf7 p7_929r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_930_1, c7_930_2, c7_930_3, c7_930_4, c7_930_5, c7_930_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_929l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_931_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_929l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_931 :
    hubcapFit theRedpart rf7 p7_929l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_931_1, c7_931_2, c7_931_3, c7_931_4, c7_931_5, c7_931_6, c7_931_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_928l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_928l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_928l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_933_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_928l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_933 :
    hubcapFit theRedpart rf7 p7_928l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_933_1, c7_933_2, c7_933_3, c7_933_4, c7_933_5, c7_933_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_935_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_935_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_935_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_935_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_926l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_935_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_926l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_935 :
    hubcapFit theRedpart rf7 p7_926l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_935_1, c7_935_2, c7_935_3, c7_935_4, c7_935_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_936_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_936_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_936_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_925l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_936_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_925l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_936_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_925l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_936 :
    hubcapFit theRedpart rf7 p7_925l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_936_1, c7_936_2, c7_936_3, c7_936_4, c7_936_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_938_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_924l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_938_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_924l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_938_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_924l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_938_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_924l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_938 :
    hubcapFit theRedpart rf7 p7_924l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_938_1, c7_938_2, c7_938_3, c7_938_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_939_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_923l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_939_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_923l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_939_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_923l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_939_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_923l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_939_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_923l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_939 :
    hubcapFit theRedpart rf7 p7_923l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_939_1, c7_939_2, c7_939_3, c7_939_4, c7_939_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_922l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_922l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_922l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_922l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_922l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_941_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_922l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_941 :
    hubcapFit theRedpart rf7 p7_922l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_941_1, c7_941_2, c7_941_3, c7_941_4, c7_941_5, c7_941_6]

end FourColor

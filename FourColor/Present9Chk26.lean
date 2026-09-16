import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 26 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1228l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1228l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1228l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1229_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1228l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1229 :
    hubcapFit theRedpart rf9 p9_1228l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1229_1, c9_1229_2, c9_1229_3, c9_1229_4, c9_1229_5, c9_1229_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1228r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1228r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1228r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1228r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1228r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1231_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1228r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1231 :
    hubcapFit theRedpart rf9 p9_1228r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1231_1, c9_1231_2, c9_1231_3, c9_1231_4, c9_1231_5, c9_1231_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1234l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1234l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1234l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1235_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1234l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1235 :
    hubcapFit theRedpart rf9 p9_1234l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1235_1, c9_1235_2, c9_1235_3, c9_1235_4, c9_1235_5, c9_1235_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1234r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1234r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1234r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1234r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1234r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1237_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1234r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1237 :
    hubcapFit theRedpart rf9 p9_1234r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1237_1, c9_1237_2, c9_1237_3, c9_1237_4, c9_1237_5, c9_1237_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1243l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1243l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1244_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1243l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1244 :
    hubcapFit theRedpart rf9 p9_1243l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1244_1, c9_1244_2, c9_1244_3, c9_1244_4, c9_1244_5, c9_1244_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1243r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1243r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1243r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1243r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1243r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1246_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1243r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1246 :
    hubcapFit theRedpart rf9 p9_1243r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1246_1, c9_1246_2, c9_1246_3, c9_1246_4, c9_1246_5, c9_1246_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1249l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1249l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1249l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1249l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1250_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1249l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1250 :
    hubcapFit theRedpart rf9 p9_1249l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1250_1, c9_1250_2, c9_1250_3, c9_1250_4, c9_1250_5, c9_1250_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1249r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1249r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1249r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1249r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1249r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1252_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1249r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1252 :
    hubcapFit theRedpart rf9 p9_1249r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1252_1, c9_1252_2, c9_1252_3, c9_1252_4, c9_1252_5, c9_1252_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1136l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1136l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1136l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1136l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1256_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1136l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1256 :
    hubcapFit theRedpart rf9 p9_1136l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1256_1, c9_1256_2, c9_1256_3, c9_1256_4, c9_1256_5, c9_1256_6, c9_1256_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1268r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1268r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1268r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1268r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1268r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1268r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1269_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1268r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1269 :
    hubcapFit theRedpart rf9 p9_1268r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1269_1, c9_1269_2, c9_1269_3, c9_1269_4, c9_1269_5, c9_1269_6, c9_1269_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1268l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1268l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1270_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1268l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1270 :
    hubcapFit theRedpart rf9 p9_1268l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1270_1, c9_1270_2, c9_1270_3, c9_1270_4, c9_1270_5, c9_1270_6, c9_1270_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1266l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1272_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1266l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1272 :
    hubcapFit theRedpart rf9 p9_1266l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1272_1, c9_1272_2, c9_1272_3, c9_1272_4, c9_1272_5, c9_1272_6, c9_1272_7, c9_1272_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1274_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1265l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1274 :
    hubcapFit theRedpart rf9 p9_1265l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1274_1, c9_1274_2, c9_1274_3, c9_1274_4, c9_1274_5, c9_1274_6, c9_1274_7, c9_1274_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1276_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1264l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1276 :
    hubcapFit theRedpart rf9 p9_1264l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1276_1, c9_1276_2, c9_1276_3, c9_1276_4, c9_1276_5, c9_1276_6, c9_1276_7, c9_1276_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1263l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1263l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1263l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1263l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1278_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1263l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1278 :
    hubcapFit theRedpart rf9 p9_1263l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1278_1, c9_1278_2, c9_1278_3, c9_1278_4, c9_1278_5, c9_1278_6, c9_1278_7, c9_1278_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1261l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1280_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1261l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1280 :
    hubcapFit theRedpart rf9 p9_1261l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1280_1, c9_1280_2, c9_1280_3, c9_1280_4, c9_1280_5, c9_1280_6, c9_1280_7]

end FourColor

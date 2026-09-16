import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 112 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5956r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5956r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5956r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5956r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5956r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5956r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5957_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5956r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5957 :
    hubcapFit theRedpart rf7 p7_5956r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5957_1, c7_5957_2, c7_5957_3, c7_5957_4, c7_5957_5, c7_5957_6, c7_5957_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5956l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5956l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5956l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5956l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5956l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5958_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5956l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5958 :
    hubcapFit theRedpart rf7 p7_5956l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5958_1, c7_5958_2, c7_5958_3, c7_5958_4, c7_5958_5, c7_5958_6, c7_5958_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5953l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5953l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5953l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5953l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5960_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5953l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5960 :
    hubcapFit theRedpart rf7 p7_5953l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5960_1, c7_5960_2, c7_5960_3, c7_5960_4, c7_5960_5, c7_5960_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5952l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5952l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5952l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5952l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5952l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5962_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5952l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5962 :
    hubcapFit theRedpart rf7 p7_5952l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5962_1, c7_5962_2, c7_5962_3, c7_5962_4, c7_5962_5, c7_5962_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5951l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5951l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5951l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5951l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5951l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5963_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5951l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5963 :
    hubcapFit theRedpart rf7 p7_5951l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5963_1, c7_5963_2, c7_5963_3, c7_5963_4, c7_5963_5, c7_5963_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5971_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5970r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5971_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5970r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5971_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5970r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5971_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5970r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5971_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5970r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5971 :
    hubcapFit theRedpart rf7 p7_5970r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5971_1, c7_5971_2, c7_5971_3, c7_5971_4, c7_5971_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5972_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5970l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5972_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5970l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5972_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5970l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5972_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5970l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5972_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5970l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5972 :
    hubcapFit theRedpart rf7 p7_5970l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5972_1, c7_5972_2, c7_5972_3, c7_5972_4, c7_5972_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5969l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5969l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5969l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5969l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5969l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5969l) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5974_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5969l) (hubSubn 7 6 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5974 :
    hubcapFit theRedpart rf7 p7_5969l
    (Hubcap.one 1 5 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 4 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5974_1, c7_5974_2, c7_5974_3, c7_5974_4, c7_5974_5, c7_5974_6, c7_5974_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5976_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5968l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5976_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5968l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5976_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5968l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5976_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5968l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5976_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5968l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5976 :
    hubcapFit theRedpart rf7 p7_5968l
    (Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5976_1, c7_5976_2, c7_5976_3, c7_5976_4, c7_5976_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5967l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5967l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5967l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5967l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5967l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5967l) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5977_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5967l) (hubSubn 7 6 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5977 :
    hubcapFit theRedpart rf7 p7_5967l
    (Hubcap.one 1 5 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 4 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5977_1, c7_5977_2, c7_5977_3, c7_5977_4, c7_5977_5, c7_5977_6, c7_5977_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5966l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5966l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5966l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5966l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5966l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5979_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5966l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5979 :
    hubcapFit theRedpart rf7 p7_5966l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5979_1, c7_5979_2, c7_5979_3, c7_5979_4, c7_5979_5, c7_5979_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5980_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5965l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5980_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5965l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5980_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5980_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5965l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5980_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5965l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5980 :
    hubcapFit theRedpart rf7 p7_5965l
    (Hubcap.one 1 5 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5980_1, c7_5980_2, c7_5980_3, c7_5980_4, c7_5980_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5982_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5949l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5982_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5949l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5982_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5949l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5982_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5949l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5982_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5949l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5982 :
    hubcapFit theRedpart rf7 p7_5949l
    (Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5982_1, c7_5982_2, c7_5982_3, c7_5982_4, c7_5982_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5985r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5985r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5985r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5985r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5985r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5986_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5985r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5986 :
    hubcapFit theRedpart rf7 p7_5985r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5986_1, c7_5986_2, c7_5986_3, c7_5986_4, c7_5986_5, c7_5986_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5985l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5985l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5985l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5985l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5985l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5987_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5985l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5987 :
    hubcapFit theRedpart rf7 p7_5985l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5987_1, c7_5987_2, c7_5987_3, c7_5987_4, c7_5987_5, c7_5987_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5989_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5984l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5989_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5984l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5989_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5984l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5989_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5984l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5989_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5984l) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5989 :
    hubcapFit theRedpart rf7 p7_5984l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5989_1, c7_5989_2, c7_5989_3, c7_5989_4, c7_5989_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6001_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6000r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6001_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6000r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6001_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6000r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6001_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6000r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6001_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6000r) (hubSubn 7 4 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6001 :
    hubcapFit theRedpart rf7 p7_6000r
    (Hubcap.one 1 5 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6001_1, c7_6001_2, c7_6001_3, c7_6001_4, c7_6001_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6002_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6000l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6002_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6000l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6002_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6002_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6000l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6002_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_6000l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6002 :
    hubcapFit theRedpart rf7 p7_6000l
    (Hubcap.one 1 5 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6002_1, c7_6002_2, c7_6002_3, c7_6002_4, c7_6002_5]

end FourColor

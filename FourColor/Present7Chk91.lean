import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 91 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4847r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4847r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4847r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4847r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4847r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4847r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4848_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4847r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4848 :
    hubcapFit theRedpart rf7 p7_4847r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4848_1, c7_4848_2, c7_4848_3, c7_4848_4, c7_4848_5, c7_4848_6, c7_4848_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4847l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4847l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4847l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4847l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4847l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4847l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4849_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4847l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4849 :
    hubcapFit theRedpart rf7 p7_4847l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4849_1, c7_4849_2, c7_4849_3, c7_4849_4, c7_4849_5, c7_4849_6, c7_4849_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4846l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4846l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4851_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4851 :
    hubcapFit theRedpart rf7 p7_4846l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4851_1, c7_4851_2, c7_4851_3, c7_4851_4, c7_4851_5, c7_4851_6, c7_4851_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4845l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4845l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4853_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4853 :
    hubcapFit theRedpart rf7 p7_4845l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4853_1, c7_4853_2, c7_4853_3, c7_4853_4, c7_4853_5, c7_4853_6, c7_4853_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4844l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4844l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4844l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4855_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4855 :
    hubcapFit theRedpart rf7 p7_4844l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4855_1, c7_4855_2, c7_4855_3, c7_4855_4, c7_4855_5, c7_4855_6, c7_4855_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4843l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4857_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4843l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4857 :
    hubcapFit theRedpart rf7 p7_4843l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4857_1, c7_4857_2, c7_4857_3, c7_4857_4, c7_4857_5, c7_4857_6, c7_4857_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4859_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4842l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4859 :
    hubcapFit theRedpart rf7 p7_4842l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4859_1, c7_4859_2, c7_4859_3, c7_4859_4, c7_4859_5, c7_4859_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4860_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4860 :
    hubcapFit theRedpart rf7 p7_4841l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4860_1, c7_4860_2, c7_4860_3, c7_4860_4, c7_4860_5, c7_4860_6, c7_4860_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4862_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4862_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4862_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4862_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4816l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4862_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4816l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4862 :
    hubcapFit theRedpart rf7 p7_4816l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4862_1, c7_4862_2, c7_4862_3, c7_4862_4, c7_4862_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4864_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4864_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4864_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4864_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4815l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4864_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4815l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4864 :
    hubcapFit theRedpart rf7 p7_4815l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4864_1, c7_4864_2, c7_4864_3, c7_4864_4, c7_4864_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4865_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4814l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4865 :
    hubcapFit theRedpart rf7 p7_4814l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4865_1, c7_4865_2, c7_4865_3, c7_4865_4, c7_4865_5, c7_4865_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4692l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4868_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4692l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4868 :
    hubcapFit theRedpart rf7 p7_4692l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4868_1, c7_4868_2, c7_4868_3, c7_4868_4, c7_4868_5, c7_4868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4882r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4882r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4882r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4882r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4882r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4882r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4883_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4882r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4883 :
    hubcapFit theRedpart rf7 p7_4882r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4883_1, c7_4883_2, c7_4883_3, c7_4883_4, c7_4883_5, c7_4883_6, c7_4883_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4882l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4882l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4882l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4882l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4882l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4882l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4884_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4882l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4884 :
    hubcapFit theRedpart rf7 p7_4882l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4884_1, c7_4884_2, c7_4884_3, c7_4884_4, c7_4884_5, c7_4884_6, c7_4884_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4881l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4881l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4881l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4881l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4881l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4881l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4886_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4881l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4886 :
    hubcapFit theRedpart rf7 p7_4881l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4886_1, c7_4886_2, c7_4886_3, c7_4886_4, c7_4886_5, c7_4886_6, c7_4886_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4880l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4880l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4880l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4880l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4880l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4880l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4888_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4880l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4888 :
    hubcapFit theRedpart rf7 p7_4880l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4888_1, c7_4888_2, c7_4888_3, c7_4888_4, c7_4888_5, c7_4888_6, c7_4888_7]

end FourColor

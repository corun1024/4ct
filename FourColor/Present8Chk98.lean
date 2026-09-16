import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 98 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4888l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4888l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4888l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4888l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4893_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4888l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4893 :
    hubcapFit theRedpart rf8 p8_4888l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4893_1, c8_4893_2, c8_4893_3, c8_4893_4, c8_4893_5, c8_4893_6, c8_4893_7, c8_4893_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4886l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4886l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4895_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4886l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4895 :
    hubcapFit theRedpart rf8 p8_4886l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4895_1, c8_4895_2, c8_4895_3, c8_4895_4, c8_4895_5, c8_4895_6, c8_4895_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4885l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4885l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4897_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4885l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4897 :
    hubcapFit theRedpart rf8 p8_4885l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4897_1, c8_4897_2, c8_4897_3, c8_4897_4, c8_4897_5, c8_4897_6, c8_4897_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4884l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4884l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4884l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4884l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4899_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4899 :
    hubcapFit theRedpart rf8 p8_4884l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4899_1, c8_4899_2, c8_4899_3, c8_4899_4, c8_4899_5, c8_4899_6, c8_4899_7, c8_4899_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4883l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4883l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4883l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4883l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4883l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4883l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4883l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4901_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4883l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4901 :
    hubcapFit theRedpart rf8 p8_4883l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4901_1, c8_4901_2, c8_4901_3, c8_4901_4, c8_4901_5, c8_4901_6, c8_4901_7, c8_4901_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4915r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4915r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4915r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4915r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4915r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4915r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4916_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4915r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4916 :
    hubcapFit theRedpart rf8 p8_4915r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4916_1, c8_4916_2, c8_4916_3, c8_4916_4, c8_4916_5, c8_4916_6, c8_4916_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4915l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4917_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4917 :
    hubcapFit theRedpart rf8 p8_4915l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4917_1, c8_4917_2, c8_4917_3, c8_4917_4, c8_4917_5, c8_4917_6, c8_4917_7, c8_4917_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4914l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4919_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4919 :
    hubcapFit theRedpart rf8 p8_4914l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4919_1, c8_4919_2, c8_4919_3, c8_4919_4, c8_4919_5, c8_4919_6, c8_4919_7, c8_4919_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4913l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4913l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4921_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4913l) (hubSubn 8 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4921 :
    hubcapFit theRedpart rf8 p8_4913l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4921_1, c8_4921_2, c8_4921_3, c8_4921_4, c8_4921_5, c8_4921_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4911l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4911l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4911l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4911l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4911l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4923_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4911l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4923 :
    hubcapFit theRedpart rf8 p8_4911l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4923_1, c8_4923_2, c8_4923_3, c8_4923_4, c8_4923_5, c8_4923_6, c8_4923_7, c8_4923_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4910l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4910l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4910l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4910l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4925_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4910l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4925 :
    hubcapFit theRedpart rf8 p8_4910l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4925_1, c8_4925_2, c8_4925_3, c8_4925_4, c8_4925_5, c8_4925_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4909l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4909l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4909l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4909l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4909l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4909l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4909l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4926_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4909l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4926 :
    hubcapFit theRedpart rf8 p8_4909l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4926_1, c8_4926_2, c8_4926_3, c8_4926_4, c8_4926_5, c8_4926_6, c8_4926_7, c8_4926_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4908l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4908l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4908l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4908l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4908l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4908l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4908l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4928_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4908l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4928 :
    hubcapFit theRedpart rf8 p8_4908l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4928_1, c8_4928_2, c8_4928_3, c8_4928_4, c8_4928_5, c8_4928_6, c8_4928_7, c8_4928_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4907l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4907l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4907l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4907l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4907l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4907l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4930_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4907l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4930 :
    hubcapFit theRedpart rf8 p8_4907l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4930_1, c8_4930_2, c8_4930_3, c8_4930_4, c8_4930_5, c8_4930_6, c8_4930_7]

end FourColor

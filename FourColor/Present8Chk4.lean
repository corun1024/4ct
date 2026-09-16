import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 4 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_200_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_200_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_182l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_200_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_182l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_200_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_182l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_200_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_182l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_200 :
    hubcapFit theRedpart rf8 p8_182l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_200_1, c8_200_2, c8_200_3, c8_200_4, c8_200_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_201_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_201_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_201_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_181l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_201_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_181l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_201_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_181l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_201 :
    hubcapFit theRedpart rf8 p8_181l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_201_1, c8_201_2, c8_201_3, c8_201_4, c8_201_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_179l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_179l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_203_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_179l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_203 :
    hubcapFit theRedpart rf8 p8_179l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_203_1, c8_203_2, c8_203_3, c8_203_4, c8_203_5, c8_203_6, c8_203_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_178l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_178l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_205_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_178l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_205 :
    hubcapFit theRedpart rf8 p8_178l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_205_1, c8_205_2, c8_205_3, c8_205_4, c8_205_5, c8_205_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_177l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_177l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_177l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_206_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_177l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_206 :
    hubcapFit theRedpart rf8 p8_177l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_206_1, c8_206_2, c8_206_3, c8_206_4, c8_206_5, c8_206_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_176l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_208_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_176l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_208 :
    hubcapFit theRedpart rf8 p8_176l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_208_1, c8_208_2, c8_208_3, c8_208_4, c8_208_5, c8_208_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_175l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_175l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_175l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_209_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_175l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_209 :
    hubcapFit theRedpart rf8 p8_175l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_209_1, c8_209_2, c8_209_3, c8_209_4, c8_209_5, c8_209_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_211_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_174l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_211_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_174l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_211_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_174l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_211_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_174l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_211 :
    hubcapFit theRedpart rf8 p8_174l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_211_1, c8_211_2, c8_211_3, c8_211_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_167l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_167l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_167l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_167l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_167l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_213_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_167l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_213 :
    hubcapFit theRedpart rf8 p8_167l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_213_1, c8_213_2, c8_213_3, c8_213_4, c8_213_5, c8_213_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_214_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_166l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_214_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_214_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_166l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_214_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_166l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_214_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_166l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_214 :
    hubcapFit theRedpart rf8 p8_166l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_214_1, c8_214_2, c8_214_3, c8_214_4, c8_214_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_216_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_216_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_165l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_216_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_165l) (hubSubn 8 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_216_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_165l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_216_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_165l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_216 :
    hubcapFit theRedpart rf8 p8_165l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_216_1, c8_216_2, c8_216_3, c8_216_4, c8_216_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_237r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_237r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_237r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_237r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_237r) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_238_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_237r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_238 :
    hubcapFit theRedpart rf8 p8_237r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_238_1, c8_238_2, c8_238_3, c8_238_4, c8_238_5, c8_238_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_237l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_237l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_237l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_239_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_237l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_239 :
    hubcapFit theRedpart rf8 p8_237l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_239_1, c8_239_2, c8_239_3, c8_239_4, c8_239_5, c8_239_6, c8_239_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_234l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_234l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_234l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_241_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_234l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_241 :
    hubcapFit theRedpart rf8 p8_234l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_241_1, c8_241_2, c8_241_3, c8_241_4, c8_241_5, c8_241_6, c8_241_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_230l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_230l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_230l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_243_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_230l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_243 :
    hubcapFit theRedpart rf8 p8_230l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_243_1, c8_243_2, c8_243_3, c8_243_4, c8_243_5, c8_243_6, c8_243_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_246_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_245r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_246_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_245r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_246_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_245r) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_246_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_245r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_246_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_245r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_246 :
    hubcapFit theRedpart rf8 p8_245r
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_246_1, c8_246_2, c8_246_3, c8_246_4, c8_246_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_245l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_245l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_247_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_245l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_247 :
    hubcapFit theRedpart rf8 p8_245l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_247_1, c8_247_2, c8_247_3, c8_247_4, c8_247_5, c8_247_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_227l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_227l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_249_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_227l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_249 :
    hubcapFit theRedpart rf8 p8_227l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_249_1, c8_249_2, c8_249_3, c8_249_4, c8_249_5, c8_249_6]

end FourColor

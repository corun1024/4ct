import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_149_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_148r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_149_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_148r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_149_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_148r) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_149_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_148r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_149_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_148r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_149 :
    hubcapFit theRedpart rf8 p8_148r
    (Hubcap.one 3 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_149_1, c8_149_2, c8_149_3, c8_149_4, c8_149_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_150_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_150_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_148l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_150_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_148l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_150_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_148l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_150_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_148l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_150 :
    hubcapFit theRedpart rf8 p8_148l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_150_1, c8_150_2, c8_150_3, c8_150_4, c8_150_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_146l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_152_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_146l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_152 :
    hubcapFit theRedpart rf8 p8_146l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_152_1, c8_152_2, c8_152_3, c8_152_4, c8_152_5, c8_152_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_154_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_145l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_154_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_145l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_154_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_145l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_154_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_145l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_154_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_145l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_154 :
    hubcapFit theRedpart rf8 p8_145l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_154_1, c8_154_2, c8_154_3, c8_154_4, c8_154_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_156_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_143l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_156_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_143l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_156_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_143l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_156_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_143l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_156 :
    hubcapFit theRedpart rf8 p8_143l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_156_1, c8_156_2, c8_156_3, c8_156_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_157_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_157_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_142l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_157_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_142l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_157_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_142l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_157_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_142l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_157 :
    hubcapFit theRedpart rf8 p8_142l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_157_1, c8_157_2, c8_157_3, c8_157_4, c8_157_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_159_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_141l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_159_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_141l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_159_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_141l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_159_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_141l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_159 :
    hubcapFit theRedpart rf8 p8_141l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_159_1, c8_159_2, c8_159_3, c8_159_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_160_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_160_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_140l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_160_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_140l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_160_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_140l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_160_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_140l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_160 :
    hubcapFit theRedpart rf8 p8_140l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_160_1, c8_160_2, c8_160_3, c8_160_4, c8_160_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_162_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_139l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_162_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_139l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_162_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_139l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_162_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_139l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_162_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_139l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_162 :
    hubcapFit theRedpart rf8 p8_139l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_162_1, c8_162_2, c8_162_3, c8_162_4, c8_162_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_163_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_138l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_163_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_138l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_163_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_138l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_163_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_138l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_163 :
    hubcapFit theRedpart rf8 p8_138l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_163_1, c8_163_2, c8_163_3, c8_163_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_170r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_170r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_170r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_170r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_170r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_170r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_171_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_170r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_171 :
    hubcapFit theRedpart rf8 p8_170r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_171_1, c8_171_2, c8_171_3, c8_171_4, c8_171_5, c8_171_6, c8_171_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_170l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_170l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_170l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_170l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_172_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_170l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_172 :
    hubcapFit theRedpart rf8 p8_170l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_172_1, c8_172_2, c8_172_3, c8_172_4, c8_172_5, c8_172_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_188r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_188r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_188r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_188r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_189_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_188r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_189 :
    hubcapFit theRedpart rf8 p8_188r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_189_1, c8_189_2, c8_189_3, c8_189_4, c8_189_5, c8_189_6, c8_189_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_188l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_188l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_190_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_188l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_190 :
    hubcapFit theRedpart rf8 p8_188l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_190_1, c8_190_2, c8_190_3, c8_190_4, c8_190_5, c8_190_6, c8_190_7, c8_190_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_192_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_186l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_192 :
    hubcapFit theRedpart rf8 p8_186l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_192_1, c8_192_2, c8_192_3, c8_192_4, c8_192_5, c8_192_6, c8_192_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_185l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_185l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_185l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_185l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_194_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_185l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_194 :
    hubcapFit theRedpart rf8 p8_185l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_194_1, c8_194_2, c8_194_3, c8_194_4, c8_194_5, c8_194_6, c8_194_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_184l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_184l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_184l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_184l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_184l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_184l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_196_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_184l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_196 :
    hubcapFit theRedpart rf8 p8_184l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_196_1, c8_196_2, c8_196_3, c8_196_4, c8_196_5, c8_196_6, c8_196_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_183l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_183l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_183l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_183l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_198_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_183l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_198 :
    hubcapFit theRedpart rf8 p8_183l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_198_1, c8_198_2, c8_198_3, c8_198_4, c8_198_5, c8_198_6, c8_198_7]

end FourColor

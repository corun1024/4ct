import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_124_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_123r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_124_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_123r) (hubSubn 6 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_124_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_123r) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_124 :
    hubcapFit theRedpart rf6 p6_123r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_124_1, c6_124_2, c6_124_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_125_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_123l) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_125_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_123l) (hubSubn 6 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_125_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_123l) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_125 :
    hubcapFit theRedpart rf6 p6_123l
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_125_1, c6_125_2, c6_125_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_129_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_128r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_129_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_128r) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_129_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_128r) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_129 :
    hubcapFit theRedpart rf6 p6_128r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_129_1, c6_129_2, c6_129_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_130_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_128l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_130_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_128l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_130_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_128l) (hubSubn 6 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_130 :
    hubcapFit theRedpart rf6 p6_128l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_130_1, c6_130_2, c6_130_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_133_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_132r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_133_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_132r) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_133_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_132r) (hubSubn 6 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_133 :
    hubcapFit theRedpart rf6 p6_132r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_133_1, c6_133_2, c6_133_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_134_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_132l) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_134_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_132l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_134_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_132l) (hubSubn 6 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_134 :
    hubcapFit theRedpart rf6 p6_132l
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_134_1, c6_134_2, c6_134_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_140_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_139r) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_140_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_139r) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_140_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_139r) (hubSubn 6 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_140 :
    hubcapFit theRedpart rf6 p6_139r
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_140_1, c6_140_2, c6_140_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_141_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_139l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_141_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_139l) (hubSubn 6 5 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_141_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_139l) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_141 :
    hubcapFit theRedpart rf6 p6_139l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_141_1, c6_141_2, c6_141_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_143_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_138l) (hubSubn 6 2 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_143_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_138l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_143_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_138l) (hubSubn 6 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_143 :
    hubcapFit theRedpart rf6 p6_138l
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_143_1, c6_143_2, c6_143_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_146_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_145r) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_146_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_145r) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_146_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_145r) (hubSubn 6 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_146 :
    hubcapFit theRedpart rf6 p6_145r
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_146_1, c6_146_2, c6_146_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_147_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_145l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_147_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_145l) (hubSubn 6 5 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_147_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_145l) (hubSubn 6 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_147 :
    hubcapFit theRedpart rf6 p6_145l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_147_1, c6_147_2, c6_147_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_149_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_144l) (hubSubn 6 2 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_149_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_144l) (hubSubn 6 5 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_149_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_144l) (hubSubn 6 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_149 :
    hubcapFit theRedpart rf6 p6_144l
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-2) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_149_1, c6_149_2, c6_149_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_159_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_158r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_159_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_158r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_159_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_158r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_159 :
    hubcapFit theRedpart rf6 p6_158r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_159_1, c6_159_2, c6_159_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_161_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_160r) (hubSubn 6 5 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_161_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_160r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_161_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_160r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_161 :
    hubcapFit theRedpart rf6 p6_160r
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_161_1, c6_161_2, c6_161_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_162_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_160l) (hubSubn 6 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_162_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_160l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_162_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_160l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_162 :
    hubcapFit theRedpart rf6 p6_160l
    (Hubcap.two 0 5 2 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_162_1, c6_162_2, c6_162_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_167_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_166r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_167_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_166r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_167_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_166r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_167 :
    hubcapFit theRedpart rf6 p6_166r
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_167_1, c6_167_2, c6_167_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_168_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_166l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_168_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_166l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_168_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_166l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_168 :
    hubcapFit theRedpart rf6 p6_166l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_168_1, c6_168_2, c6_168_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_170_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_165l) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_170_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_165l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_170_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_165l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_170 :
    hubcapFit theRedpart rf6 p6_165l
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_170_1, c6_170_2, c6_170_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_176_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_175r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_176_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_175r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_176_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_175r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_176 :
    hubcapFit theRedpart rf6 p6_175r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_176_1, c6_176_2, c6_176_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_177_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_175l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_177_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_175l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_177_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_175l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_177 :
    hubcapFit theRedpart rf6 p6_175l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_177_1, c6_177_2, c6_177_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_179_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_174l) (hubSubn 6 5 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_179_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_174l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_179_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_174l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_179 :
    hubcapFit theRedpart rf6 p6_174l
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_179_1, c6_179_2, c6_179_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_182_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_181r) (hubSubn 6 5 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_182_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_181r) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_182_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_181r) (hubSubn 6 4 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_182 :
    hubcapFit theRedpart rf6 p6_181r
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_182_1, c6_182_2, c6_182_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_183_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_181l) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_183_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_181l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_183_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_181l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_183 :
    hubcapFit theRedpart rf6 p6_181l
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_183_1, c6_183_2, c6_183_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_185_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_180l) (hubSubn 6 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_185_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_180l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_185_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_180l) (hubSubn 6 4 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_185 :
    hubcapFit theRedpart rf6 p6_180l
    (Hubcap.two 0 5 2 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_185_1, c6_185_2, c6_185_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_189_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_188r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_189_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_188r) (hubSubn 6 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_189_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_188r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_189 :
    hubcapFit theRedpart rf6 p6_188r
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_189_1, c6_189_2, c6_189_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_190_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_188l) (hubSubn 6 5 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_190_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_188l) (hubSubn 6 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_190_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_188l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_190 :
    hubcapFit theRedpart rf6 p6_188l
    (Hubcap.two 0 5 (-2) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_190_1, c6_190_2, c6_190_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_192_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_187l) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_192_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_187l) (hubSubn 6 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_192_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_187l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_192 :
    hubcapFit theRedpart rf6 p6_187l
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_192_1, c6_192_2, c6_192_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_198_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_197r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_198_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_197r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_198_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_197r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_198 :
    hubcapFit theRedpart rf6 p6_197r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_198_1, c6_198_2, c6_198_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_199_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_197l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_199_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_197l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_199_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_197l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_199 :
    hubcapFit theRedpart rf6 p6_197l
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_199_1, c6_199_2, c6_199_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_201_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_196l) (hubSubn 6 5 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_201_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_196l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_201_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_196l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_201 :
    hubcapFit theRedpart rf6 p6_196l
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_201_1, c6_201_2, c6_201_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_204_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_203r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_204_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_203r) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_204_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_203r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_204 :
    hubcapFit theRedpart rf6 p6_203r
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_204_1, c6_204_2, c6_204_3]

end FourColor

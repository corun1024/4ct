import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 3 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_94l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_94l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_94l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_94l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_94l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_94l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_125_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_94l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_125 :
    hubcapFit theRedpart rf9 p9_94l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_125_1, c9_125_2, c9_125_3, c9_125_4, c9_125_5, c9_125_6, c9_125_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_93l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_93l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_93l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_93l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_93l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_93l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_127_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_93l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_127 :
    hubcapFit theRedpart rf9 p9_93l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_127_1, c9_127_2, c9_127_3, c9_127_4, c9_127_5, c9_127_6, c9_127_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_92l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_92l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_92l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_92l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_92l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_129_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_92l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_129 :
    hubcapFit theRedpart rf9 p9_92l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_129_1, c9_129_2, c9_129_3, c9_129_4, c9_129_5, c9_129_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_91l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_91l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_91l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_91l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_91l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_130_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_91l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_130 :
    hubcapFit theRedpart rf9 p9_91l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_130_1, c9_130_2, c9_130_3, c9_130_4, c9_130_5, c9_130_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_90l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_90l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_90l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_90l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_90l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_132_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_90l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_132 :
    hubcapFit theRedpart rf9 p9_90l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_132_1, c9_132_2, c9_132_3, c9_132_4, c9_132_5, c9_132_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_89l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_89l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_89l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_89l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_89l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_133_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_89l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_133 :
    hubcapFit theRedpart rf9 p9_89l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_133_1, c9_133_2, c9_133_3, c9_133_4, c9_133_5, c9_133_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_88l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_88l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_88l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_88l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_88l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_88l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_135_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_88l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_135 :
    hubcapFit theRedpart rf9 p9_88l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_135_1, c9_135_2, c9_135_3, c9_135_4, c9_135_5, c9_135_6, c9_135_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_163r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_163r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_163r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_163r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_163r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_163r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_163r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_164_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_163r) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_164 :
    hubcapFit theRedpart rf9 p9_163r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_164_1, c9_164_2, c9_164_3, c9_164_4, c9_164_5, c9_164_6, c9_164_7, c9_164_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_163l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_163l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_163l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_165_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_163l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_165 :
    hubcapFit theRedpart rf9 p9_163l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_165_1, c9_165_2, c9_165_3, c9_165_4, c9_165_5, c9_165_6, c9_165_7, c9_165_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_162l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_162l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_162l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_162l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_162l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_167_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_162l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_167 :
    hubcapFit theRedpart rf9 p9_162l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_167_1, c9_167_2, c9_167_3, c9_167_4, c9_167_5, c9_167_6, c9_167_7, c9_167_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_161l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_161l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_169_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_161l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_169 :
    hubcapFit theRedpart rf9 p9_161l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_169_1, c9_169_2, c9_169_3, c9_169_4, c9_169_5, c9_169_6, c9_169_7, c9_169_8, c9_169_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_160l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_160l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_160l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_160l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_171_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_160l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_171 :
    hubcapFit theRedpart rf9 p9_160l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_171_1, c9_171_2, c9_171_3, c9_171_4, c9_171_5, c9_171_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_173l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_173l) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_174_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_173l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_174 :
    hubcapFit theRedpart rf9 p9_173l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_174_1, c9_174_2, c9_174_3, c9_174_4, c9_174_5, c9_174_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_173r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_173r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_173r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_173r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_173r) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_176_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_173r) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_176 :
    hubcapFit theRedpart rf9 p9_173r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_176_1, c9_176_2, c9_176_3, c9_176_4, c9_176_5, c9_176_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_180_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_179l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_180_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_179l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_180_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_179l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_180_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_179l) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_180_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_179l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_180 :
    hubcapFit theRedpart rf9 p9_179l
    (Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_180_1, c9_180_2, c9_180_3, c9_180_4, c9_180_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_182_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_179r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_182_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_179r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_182_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_179r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_182_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_179r) (hubSubn 9 8 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_182_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_179r) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_182 :
    hubcapFit theRedpart rf9 p9_179r
    (Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 8 7 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_182_1, c9_182_2, c9_182_3, c9_182_4, c9_182_5]

end FourColor

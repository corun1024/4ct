import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_105_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_103l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_105_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_103l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_105_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_103l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_105_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_103l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_105 :
    hubcapFit theRedpart rf7 p7_103l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_105_1, c7_105_2, c7_105_3, c7_105_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_107_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_102l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_107_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_102l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_107_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_102l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_107_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_102l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_107 :
    hubcapFit theRedpart rf7 p7_102l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_107_1, c7_107_2, c7_107_3, c7_107_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_108_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_101l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_108_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_101l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_108_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_101l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_108_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_101l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_108 :
    hubcapFit theRedpart rf7 p7_101l
    (Hubcap.one 0 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_108_1, c7_108_2, c7_108_3, c7_108_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_110_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_100l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_110_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_100l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_110_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_100l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_110_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_100l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_110 :
    hubcapFit theRedpart rf7 p7_100l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_110_1, c7_110_2, c7_110_3, c7_110_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_112_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_87l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_112_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_87l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_112_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_87l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_112_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_87l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_112 :
    hubcapFit theRedpart rf7 p7_87l
    (Hubcap.one 0 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_112_1, c7_112_2, c7_112_3, c7_112_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_113_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_86l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_113_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_86l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_113_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_86l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_113_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_86l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_113_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_86l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_113 :
    hubcapFit theRedpart rf7 p7_86l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_113_1, c7_113_2, c7_113_3, c7_113_4, c7_113_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_115_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_85l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_115_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_85l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_115_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_85l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_115_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_85l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_115_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_85l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_115 :
    hubcapFit theRedpart rf7 p7_85l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_115_1, c7_115_2, c7_115_3, c7_115_4, c7_115_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_116_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_84l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_116_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_84l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_116_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_84l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_116_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_84l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_116_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_84l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_116 :
    hubcapFit theRedpart rf7 p7_84l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_116_1, c7_116_2, c7_116_3, c7_116_4, c7_116_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_118_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_83l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_118_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_83l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_118_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_83l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_118_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_83l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_118 :
    hubcapFit theRedpart rf7 p7_83l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_118_1, c7_118_2, c7_118_3, c7_118_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_138_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_137r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_138_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_137r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_138_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_137r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_138_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_137r) (hubSubn 7 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_138_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_137r) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_138 :
    hubcapFit theRedpart rf7 p7_137r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_138_1, c7_138_2, c7_138_3, c7_138_4, c7_138_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_139_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_137l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_139_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_137l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_139_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_139_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_137l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_139_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_137l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_139 :
    hubcapFit theRedpart rf7 p7_137l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_139_1, c7_139_2, c7_139_3, c7_139_4, c7_139_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_141_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_136l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_141_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_141_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_136l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_141_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_136l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_141_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_136l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_141 :
    hubcapFit theRedpart rf7 p7_136l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_141_1, c7_141_2, c7_141_3, c7_141_4, c7_141_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_142_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_135l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_142_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_135l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_142_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_135l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_142_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_135l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_142_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_135l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_142 :
    hubcapFit theRedpart rf7 p7_135l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_142_1, c7_142_2, c7_142_3, c7_142_4, c7_142_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_144_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_134l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_144_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_134l) (hubSubn 7 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_144_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_134l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_144_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_134l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_144 :
    hubcapFit theRedpart rf7 p7_134l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_144_1, c7_144_2, c7_144_3, c7_144_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_145_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_145_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_133l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_145_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_133l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_145_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_133l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_145_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_133l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_145 :
    hubcapFit theRedpart rf7 p7_133l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_145_1, c7_145_2, c7_145_3, c7_145_4, c7_145_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_147_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_147_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_132l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_147_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_147_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_132l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_147_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_132l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_147 :
    hubcapFit theRedpart rf7 p7_132l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_147_1, c7_147_2, c7_147_3, c7_147_4, c7_147_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_148_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_131l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_148_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_131l) (hubSubn 7 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_148_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_131l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_148_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_131l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_148 :
    hubcapFit theRedpart rf7 p7_131l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_148_1, c7_148_2, c7_148_3, c7_148_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_150_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_130l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_150_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_130l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_150_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_130l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_150_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_130l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_150_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_130l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_150 :
    hubcapFit theRedpart rf7 p7_130l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_150_1, c7_150_2, c7_150_3, c7_150_4, c7_150_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_151_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_151_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_151_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_129l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_151_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_129l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_151_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_129l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_151 :
    hubcapFit theRedpart rf7 p7_129l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_151_1, c7_151_2, c7_151_3, c7_151_4, c7_151_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_153_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_128l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_153_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_128l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_153_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_128l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_153_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_128l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_153_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_128l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_153 :
    hubcapFit theRedpart rf7 p7_128l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_153_1, c7_153_2, c7_153_3, c7_153_4, c7_153_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_154_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_127l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_154_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_127l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_154_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_127l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_154_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_127l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_154_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_127l) (hubSubn 7 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_154 :
    hubcapFit theRedpart rf7 p7_127l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_154_1, c7_154_2, c7_154_3, c7_154_4, c7_154_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_156_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_126l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_156_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_126l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_156_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_126l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_156_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_126l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_156_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_126l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_156 :
    hubcapFit theRedpart rf7 p7_126l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_156_1, c7_156_2, c7_156_3, c7_156_4, c7_156_5]

end FourColor

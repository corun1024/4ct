import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_60l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_60l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_60l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_60l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_60l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_83_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_60l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_83 :
    hubcapFit theRedpart rf8 p8_60l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_83_1, c8_83_2, c8_83_3, c8_83_4, c8_83_5, c8_83_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_59l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_59l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_59l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_59l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_59l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_85_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_59l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_85 :
    hubcapFit theRedpart rf8 p8_59l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_85_1, c8_85_2, c8_85_3, c8_85_4, c8_85_5, c8_85_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_58l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_58l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_58l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_58l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_58l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_86_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_58l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_86 :
    hubcapFit theRedpart rf8 p8_58l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_86_1, c8_86_2, c8_86_3, c8_86_4, c8_86_5, c8_86_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_57l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_57l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_57l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_57l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_57l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_88_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_57l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_88 :
    hubcapFit theRedpart rf8 p8_57l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_88_1, c8_88_2, c8_88_3, c8_88_4, c8_88_5, c8_88_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_90_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_24l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_90_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_24l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_90_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_24l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_90_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_24l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_90 :
    hubcapFit theRedpart rf8 p8_24l
    (Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_90_1, c8_90_2, c8_90_3, c8_90_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_91_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_23l) (hubSubn 8 7 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_91_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_23l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_91_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_23l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_91_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_23l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_91 :
    hubcapFit theRedpart rf8 p8_23l
    (Hubcap.two 0 7 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_91_1, c8_91_2, c8_91_3, c8_91_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_93_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_22l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_93_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_22l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_93_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_22l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_93_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_22l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_93 :
    hubcapFit theRedpart rf8 p8_22l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_93_1, c8_93_2, c8_93_3, c8_93_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_94_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_21l) (hubSubn 8 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_94_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_21l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_94_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_21l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_94_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_21l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_94 :
    hubcapFit theRedpart rf8 p8_21l
    (Hubcap.two 0 7 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_94_1, c8_94_2, c8_94_3, c8_94_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_96_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_20l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_96_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_20l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_96_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_20l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_96_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_20l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_96 :
    hubcapFit theRedpart rf8 p8_20l
    (Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_96_1, c8_96_2, c8_96_3, c8_96_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_97_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_19l) (hubSubn 8 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_97_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_19l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_97_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_19l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_97_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_19l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_97 :
    hubcapFit theRedpart rf8 p8_19l
    (Hubcap.two 0 7 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_97_1, c8_97_2, c8_97_3, c8_97_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_99_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_18l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_99_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_18l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_99_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_18l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_99_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_18l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_99 :
    hubcapFit theRedpart rf8 p8_18l
    (Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_99_1, c8_99_2, c8_99_3, c8_99_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_100_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_17l) (hubSubn 8 7 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_100_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_17l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_100_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_17l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_100_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_17l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_100 :
    hubcapFit theRedpart rf8 p8_17l
    (Hubcap.two 0 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_100_1, c8_100_2, c8_100_3, c8_100_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_16l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_16l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_16l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_16l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_16l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_102_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_16l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_102 :
    hubcapFit theRedpart rf8 p8_16l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 0 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_102_1, c8_102_2, c8_102_3, c8_102_4, c8_102_5, c8_102_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_15l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_15l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_15l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_15l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_15l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_103_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_15l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_103 :
    hubcapFit theRedpart rf8 p8_15l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_103_1, c8_103_2, c8_103_3, c8_103_4, c8_103_5, c8_103_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_14l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_14l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_14l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_14l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_14l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_105_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_14l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_105 :
    hubcapFit theRedpart rf8 p8_14l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_105_1, c8_105_2, c8_105_3, c8_105_4, c8_105_5, c8_105_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_13l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_13l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_13l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_13l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_13l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_106_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_13l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_106 :
    hubcapFit theRedpart rf8 p8_13l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_106_1, c8_106_2, c8_106_3, c8_106_4, c8_106_5, c8_106_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_12l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_12l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_12l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_12l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_12l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_108_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_12l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_108 :
    hubcapFit theRedpart rf8 p8_12l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_108_1, c8_108_2, c8_108_3, c8_108_4, c8_108_5, c8_108_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_11l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_11l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_11l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_11l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_11l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_109_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_11l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_109 :
    hubcapFit theRedpart rf8 p8_11l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_109_1, c8_109_2, c8_109_3, c8_109_4, c8_109_5, c8_109_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_10l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_10l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_10l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_10l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_10l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_111_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_10l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_111 :
    hubcapFit theRedpart rf8 p8_10l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_111_1, c8_111_2, c8_111_3, c8_111_4, c8_111_5, c8_111_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_9l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_9l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_9l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_9l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_9l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_112_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_9l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_112 :
    hubcapFit theRedpart rf8 p8_9l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_112_1, c8_112_2, c8_112_3, c8_112_4, c8_112_5, c8_112_6]

end FourColor

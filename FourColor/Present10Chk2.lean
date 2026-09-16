import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_76l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_76l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_76l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_76l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_76l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_76l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_76l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_76l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_77_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_76l) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_77 :
    hubcapFit theRedpart rf10 p10_76l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_77_1, c10_77_2, c10_77_3, c10_77_4, c10_77_5, c10_77_6, c10_77_7, c10_77_8, c10_77_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_76r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_76r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_76r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_76r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_76r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_76r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_76r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_76r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_79_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_76r) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_79 :
    hubcapFit theRedpart rf10 p10_76r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_79_1, c10_79_2, c10_79_3, c10_79_4, c10_79_5, c10_79_6, c10_79_7, c10_79_8, c10_79_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_82l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_82l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_82l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_82l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_82l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_82l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_82l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_82l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_83_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_82l) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_83 :
    hubcapFit theRedpart rf10 p10_82l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_83_1, c10_83_2, c10_83_3, c10_83_4, c10_83_5, c10_83_6, c10_83_7, c10_83_8, c10_83_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_82r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_82r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_82r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_82r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_82r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_82r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_82r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_82r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_85_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_82r) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_85 :
    hubcapFit theRedpart rf10 p10_82r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_85_1, c10_85_2, c10_85_3, c10_85_4, c10_85_5, c10_85_6, c10_85_7, c10_85_8, c10_85_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_74r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_74r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_74r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_74r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_74r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_74r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_74r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_74r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_89_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_74r) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_89 :
    hubcapFit theRedpart rf10 p10_74r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_89_1, c10_89_2, c10_89_3, c10_89_4, c10_89_5, c10_89_6, c10_89_7, c10_89_8, c10_89_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_73r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_73r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_73r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_73r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_73r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_73r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_73r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_73r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_92_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_73r) (hubSubn 10 9 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_92 :
    hubcapFit theRedpart rf10 p10_73r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_92_1, c10_92_2, c10_92_3, c10_92_4, c10_92_5, c10_92_6, c10_92_7, c10_92_8, c10_92_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_128_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_128 :
    hubcapFit theRedpart rf10 p10_127r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_128_1, c10_128_2, c10_128_3, c10_128_4, c10_128_5, c10_128_6, c10_128_7, c10_128_8, c10_128_9, c10_128_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_141r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_141r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_141r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_141r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_141r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_141r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_141r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_141r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_142_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_141r) (hubSubn 10 6 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_142 :
    hubcapFit theRedpart rf10 p10_141r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 4 <|
     Hubcap.two 3 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_142_1, c10_142_2, c10_142_3, c10_142_4, c10_142_5, c10_142_6, c10_142_7, c10_142_8, c10_142_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_137l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_137l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_137l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_137l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_144_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_137l) (hubSubn 10 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_144 :
    hubcapFit theRedpart rf10 p10_137l
    (Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_144_1, c10_144_2, c10_144_3, c10_144_4, c10_144_5, c10_144_6, c10_144_7, c10_144_8, c10_144_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_136l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_136l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_136l) (hubSubn 10 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_136l) (hubSubn 10 8 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_146_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_136l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_146 :
    hubcapFit theRedpart rf10 p10_136l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 3 8 8 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_146_1, c10_146_2, c10_146_3, c10_146_4, c10_146_5, c10_146_6, c10_146_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_164r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_164r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_164r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_164r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_164r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_164r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_164r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_164r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_165_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_164r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_165 :
    hubcapFit theRedpart rf10 p10_164r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_165_1, c10_165_2, c10_165_3, c10_165_4, c10_165_5, c10_165_6, c10_165_7, c10_165_8, c10_165_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_164l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_164l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_164l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_166_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_164l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_166 :
    hubcapFit theRedpart rf10 p10_164l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_166_1, c10_166_2, c10_166_3, c10_166_4, c10_166_5, c10_166_6, c10_166_7, c10_166_8, c10_166_9, c10_166_10]

end FourColor

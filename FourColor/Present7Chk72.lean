import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 72 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3851l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3851l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3851l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3880_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3851l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3880 :
    hubcapFit theRedpart rf7 p7_3851l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3880_1, c7_3880_2, c7_3880_3, c7_3880_4, c7_3880_5, c7_3880_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3850l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3850l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3882_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3850l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3882 :
    hubcapFit theRedpart rf7 p7_3850l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3882_1, c7_3882_2, c7_3882_3, c7_3882_4, c7_3882_5, c7_3882_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3884_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3884_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3884_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3809l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3884_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3809l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3884_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3809l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3884 :
    hubcapFit theRedpart rf7 p7_3809l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3884_1, c7_3884_2, c7_3884_3, c7_3884_4, c7_3884_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3808l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3808l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3808l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3885_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3808l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3885 :
    hubcapFit theRedpart rf7 p7_3808l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3885_1, c7_3885_2, c7_3885_3, c7_3885_4, c7_3885_5, c7_3885_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3900r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3900r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3900r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3900r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3900r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3900r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3901_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3900r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3901 :
    hubcapFit theRedpart rf7 p7_3900r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3901_1, c7_3901_2, c7_3901_3, c7_3901_4, c7_3901_5, c7_3901_6, c7_3901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3900l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3900l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3900l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3900l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3900l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3900l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3902_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3900l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3902 :
    hubcapFit theRedpart rf7 p7_3900l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3902_1, c7_3902_2, c7_3902_3, c7_3902_4, c7_3902_5, c7_3902_6, c7_3902_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3899l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3899l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3899l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3899l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3904_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3899l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3904 :
    hubcapFit theRedpart rf7 p7_3899l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3904_1, c7_3904_2, c7_3904_3, c7_3904_4, c7_3904_5, c7_3904_6, c7_3904_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3896l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3896l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3896l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3896l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3896l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3896l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3906_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3896l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3906 :
    hubcapFit theRedpart rf7 p7_3896l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3906_1, c7_3906_2, c7_3906_3, c7_3906_4, c7_3906_5, c7_3906_6, c7_3906_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3894l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3894l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3894l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3908_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3894l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3908 :
    hubcapFit theRedpart rf7 p7_3894l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3908_1, c7_3908_2, c7_3908_3, c7_3908_4, c7_3908_5, c7_3908_6, c7_3908_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3893l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3893l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3910_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3893l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3910 :
    hubcapFit theRedpart rf7 p7_3893l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3910_1, c7_3910_2, c7_3910_3, c7_3910_4, c7_3910_5, c7_3910_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3892l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3911_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3892l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3911 :
    hubcapFit theRedpart rf7 p7_3892l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3911_1, c7_3911_2, c7_3911_3, c7_3911_4, c7_3911_5, c7_3911_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3891l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3891l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3891l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3891l) (hubSubn 7 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3913_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3891l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3913 :
    hubcapFit theRedpart rf7 p7_3891l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3913_1, c7_3913_2, c7_3913_3, c7_3913_4, c7_3913_5, c7_3913_6, c7_3913_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3889l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3889l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3889l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3889l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3889l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3915_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3889l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3915 :
    hubcapFit theRedpart rf7 p7_3889l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3915_1, c7_3915_2, c7_3915_3, c7_3915_4, c7_3915_5, c7_3915_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3888l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3888l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3888l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3888l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3917_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3888l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3917 :
    hubcapFit theRedpart rf7 p7_3888l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3917_1, c7_3917_2, c7_3917_3, c7_3917_4, c7_3917_5, c7_3917_6, c7_3917_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3887l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3887l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3887l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3887l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3887l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3919_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3887l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3919 :
    hubcapFit theRedpart rf7 p7_3887l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3919_1, c7_3919_2, c7_3919_3, c7_3919_4, c7_3919_5, c7_3919_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3934r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3934r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3934r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3934r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3934r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3935_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3934r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3935 :
    hubcapFit theRedpart rf7 p7_3934r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3935_1, c7_3935_2, c7_3935_3, c7_3935_4, c7_3935_5, c7_3935_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3934l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3934l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3936_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3934l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3936 :
    hubcapFit theRedpart rf7 p7_3934l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3936_1, c7_3936_2, c7_3936_3, c7_3936_4, c7_3936_5, c7_3936_6]

end FourColor

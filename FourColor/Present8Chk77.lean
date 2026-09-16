import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 77 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3873l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3873l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3873l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3873l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3873l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3875_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3873l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3875 :
    hubcapFit theRedpart rf8 p8_3873l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3875_1, c8_3875_2, c8_3875_3, c8_3875_4, c8_3875_5, c8_3875_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3872l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3872l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3872l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3872l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3872l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3872l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3872l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3877_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3872l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3877 :
    hubcapFit theRedpart rf8 p8_3872l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3877_1, c8_3877_2, c8_3877_3, c8_3877_4, c8_3877_5, c8_3877_6, c8_3877_7, c8_3877_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3871l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3871l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3871l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3879_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3871l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3879 :
    hubcapFit theRedpart rf8 p8_3871l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3879_1, c8_3879_2, c8_3879_3, c8_3879_4, c8_3879_5, c8_3879_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3870l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3870l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3870l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3880_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3870l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3880 :
    hubcapFit theRedpart rf8 p8_3870l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3880_1, c8_3880_2, c8_3880_3, c8_3880_4, c8_3880_5, c8_3880_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3628l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3628l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3628l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3883_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3628l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3883 :
    hubcapFit theRedpart rf8 p8_3628l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3883_1, c8_3883_2, c8_3883_3, c8_3883_4, c8_3883_5, c8_3883_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3627l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3627l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3627l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3627l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3627l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3885_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3627l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3885 :
    hubcapFit theRedpart rf8 p8_3627l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3885_1, c8_3885_2, c8_3885_3, c8_3885_4, c8_3885_5, c8_3885_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3895r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3895r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3895r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3896_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3895r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3896 :
    hubcapFit theRedpart rf8 p8_3895r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3896_1, c8_3896_2, c8_3896_3, c8_3896_4, c8_3896_5, c8_3896_6, c8_3896_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3895l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3895l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3897_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3895l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3897 :
    hubcapFit theRedpart rf8 p8_3895l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3897_1, c8_3897_2, c8_3897_3, c8_3897_4, c8_3897_5, c8_3897_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3899_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3894l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3899 :
    hubcapFit theRedpart rf8 p8_3894l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3899_1, c8_3899_2, c8_3899_3, c8_3899_4, c8_3899_5, c8_3899_6, c8_3899_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3893l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3893l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3901_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3893l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3901 :
    hubcapFit theRedpart rf8 p8_3893l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3901_1, c8_3901_2, c8_3901_3, c8_3901_4, c8_3901_5, c8_3901_6, c8_3901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3892l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3892l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3903_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3892l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3903 :
    hubcapFit theRedpart rf8 p8_3892l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3903_1, c8_3903_2, c8_3903_3, c8_3903_4, c8_3903_5, c8_3903_6, c8_3903_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3905_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3891l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3905 :
    hubcapFit theRedpart rf8 p8_3891l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3905_1, c8_3905_2, c8_3905_3, c8_3905_4, c8_3905_5, c8_3905_6, c8_3905_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3890l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3890l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3907_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3890l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3907 :
    hubcapFit theRedpart rf8 p8_3890l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3907_1, c8_3907_2, c8_3907_3, c8_3907_4, c8_3907_5, c8_3907_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3889l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3889l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3889l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3889l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3908_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3889l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3908 :
    hubcapFit theRedpart rf8 p8_3889l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3908_1, c8_3908_2, c8_3908_3, c8_3908_4, c8_3908_5, c8_3908_6, c8_3908_7, c8_3908_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3888l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3888l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3910_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3888l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3910 :
    hubcapFit theRedpart rf8 p8_3888l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3910_1, c8_3910_2, c8_3910_3, c8_3910_4, c8_3910_5, c8_3910_6, c8_3910_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3887l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3887l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3887l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3887l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3887l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3912_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3887l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3912 :
    hubcapFit theRedpart rf8 p8_3887l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3912_1, c8_3912_2, c8_3912_3, c8_3912_4, c8_3912_5, c8_3912_6]

end FourColor

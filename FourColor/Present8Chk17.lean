import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 17 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_837l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_837l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_837l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_860_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_837l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_860 :
    hubcapFit theRedpart rf8 p8_837l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_860_1, c8_860_2, c8_860_3, c8_860_4, c8_860_5, c8_860_6, c8_860_7, c8_860_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_836l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_836l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_836l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_862_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_836l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_862 :
    hubcapFit theRedpart rf8 p8_836l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_862_1, c8_862_2, c8_862_3, c8_862_4, c8_862_5, c8_862_6, c8_862_7, c8_862_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_820l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_820l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_820l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_820l) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_864_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_820l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_864 :
    hubcapFit theRedpart rf8 p8_820l
    (Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_864_1, c8_864_2, c8_864_3, c8_864_4, c8_864_5, c8_864_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_871_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_870r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_871_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_870r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_871_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_870r) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_871_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_870r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_871_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_870r) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_871 :
    hubcapFit theRedpart rf8 p8_870r
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_871_1, c8_871_2, c8_871_3, c8_871_4, c8_871_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_870l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_870l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_872_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_870l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_872 :
    hubcapFit theRedpart rf8 p8_870l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_872_1, c8_872_2, c8_872_3, c8_872_4, c8_872_5, c8_872_6, c8_872_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_868l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_868l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_868l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_868l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_874_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_868l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_874 :
    hubcapFit theRedpart rf8 p8_868l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_874_1, c8_874_2, c8_874_3, c8_874_4, c8_874_5, c8_874_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_876_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_818l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_876_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_818l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_876_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_818l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_876_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_818l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_876_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_818l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_876 :
    hubcapFit theRedpart rf8 p8_818l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_876_1, c8_876_2, c8_876_3, c8_876_4, c8_876_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_878_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_817l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_878_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_817l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_878_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_817l) (hubSubn 8 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_878_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_817l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_878_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_817l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_878 :
    hubcapFit theRedpart rf8 p8_817l
    (Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_878_1, c8_878_2, c8_878_3, c8_878_4, c8_878_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_816l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_816l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_816l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_816l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_816l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_879_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_816l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_879 :
    hubcapFit theRedpart rf8 p8_816l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_879_1, c8_879_2, c8_879_3, c8_879_4, c8_879_5, c8_879_6, c8_879_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_815l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_815l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_815l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_815l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_815l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_881_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_815l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_881 :
    hubcapFit theRedpart rf8 p8_815l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_881_1, c8_881_2, c8_881_3, c8_881_4, c8_881_5, c8_881_6, c8_881_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_897r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_897r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_897r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_897r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_897r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_897r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_897r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_898_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_897r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_898 :
    hubcapFit theRedpart rf8 p8_897r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_898_1, c8_898_2, c8_898_3, c8_898_4, c8_898_5, c8_898_6, c8_898_7, c8_898_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_897l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_897l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_899_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_897l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_899 :
    hubcapFit theRedpart rf8 p8_897l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_899_1, c8_899_2, c8_899_3, c8_899_4, c8_899_5, c8_899_6, c8_899_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_895l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_895l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_895l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_901_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_895l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_901 :
    hubcapFit theRedpart rf8 p8_895l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_901_1, c8_901_2, c8_901_3, c8_901_4, c8_901_5, c8_901_6, c8_901_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_894l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_894l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_903_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_894l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_903 :
    hubcapFit theRedpart rf8 p8_894l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_903_1, c8_903_2, c8_903_3, c8_903_4, c8_903_5, c8_903_6, c8_903_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_892l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_892l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_905_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_892l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_905 :
    hubcapFit theRedpart rf8 p8_892l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_905_1, c8_905_2, c8_905_3, c8_905_4, c8_905_5, c8_905_6, c8_905_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_891l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_891l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_907_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_891l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_907 :
    hubcapFit theRedpart rf8 p8_891l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_907_1, c8_907_2, c8_907_3, c8_907_4, c8_907_5, c8_907_6, c8_907_7]

end FourColor

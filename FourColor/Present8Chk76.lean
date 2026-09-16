import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 76 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3821l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3821l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3821l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3821l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3834_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3821l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3834 :
    hubcapFit theRedpart rf8 p8_3821l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3834_1, c8_3834_2, c8_3834_3, c8_3834_4, c8_3834_5, c8_3834_6, c8_3834_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3820l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3820l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3820l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3836_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3820l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3836 :
    hubcapFit theRedpart rf8 p8_3820l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3836_1, c8_3836_2, c8_3836_3, c8_3836_4, c8_3836_5, c8_3836_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3841r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3841r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3841r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3841r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3841r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3842_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3841r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3842 :
    hubcapFit theRedpart rf8 p8_3841r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3842_1, c8_3842_2, c8_3842_3, c8_3842_4, c8_3842_5, c8_3842_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3841l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3841l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3843_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3841l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3843 :
    hubcapFit theRedpart rf8 p8_3841l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3843_1, c8_3843_2, c8_3843_3, c8_3843_4, c8_3843_5, c8_3843_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3840l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3840l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3840l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3845_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3840l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3845 :
    hubcapFit theRedpart rf8 p8_3840l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3845_1, c8_3845_2, c8_3845_3, c8_3845_4, c8_3845_5, c8_3845_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3839l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3839l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3846_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3839l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3846 :
    hubcapFit theRedpart rf8 p8_3839l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3846_1, c8_3846_2, c8_3846_3, c8_3846_4, c8_3846_5, c8_3846_6, c8_3846_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3838l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3838l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3848_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3838l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3848 :
    hubcapFit theRedpart rf8 p8_3838l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3848_1, c8_3848_2, c8_3848_3, c8_3848_4, c8_3848_5, c8_3848_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3854r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3854r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3854r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3854r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3854r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3854r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3855_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3854r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3855 :
    hubcapFit theRedpart rf8 p8_3854r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3855_1, c8_3855_2, c8_3855_3, c8_3855_4, c8_3855_5, c8_3855_6, c8_3855_7, c8_3855_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3854l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3856_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3854l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3856 :
    hubcapFit theRedpart rf8 p8_3854l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3856_1, c8_3856_2, c8_3856_3, c8_3856_4, c8_3856_5, c8_3856_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3858_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3853l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3858 :
    hubcapFit theRedpart rf8 p8_3853l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3858_1, c8_3858_2, c8_3858_3, c8_3858_4, c8_3858_5, c8_3858_6, c8_3858_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3852l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3860_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3852l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3860 :
    hubcapFit theRedpart rf8 p8_3852l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3860_1, c8_3860_2, c8_3860_3, c8_3860_4, c8_3860_5, c8_3860_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3851l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3851l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3851l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3861_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3851l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3861 :
    hubcapFit theRedpart rf8 p8_3851l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3861_1, c8_3861_2, c8_3861_3, c8_3861_4, c8_3861_5, c8_3861_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3816l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3816l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3816l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3863_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3816l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3863 :
    hubcapFit theRedpart rf8 p8_3816l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3863_1, c8_3863_2, c8_3863_3, c8_3863_4, c8_3863_5, c8_3863_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3815l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3815l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3865_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3815l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3865 :
    hubcapFit theRedpart rf8 p8_3815l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3865_1, c8_3865_2, c8_3865_3, c8_3865_4, c8_3865_5, c8_3865_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3814l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3814l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3814l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3866_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3814l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3866 :
    hubcapFit theRedpart rf8 p8_3814l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3866_1, c8_3866_2, c8_3866_3, c8_3866_4, c8_3866_5, c8_3866_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3813l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3813l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3813l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3868_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3813l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3868 :
    hubcapFit theRedpart rf8 p8_3813l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3868_1, c8_3868_2, c8_3868_3, c8_3868_4, c8_3868_5, c8_3868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3873r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3873r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3873r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3873r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3873r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3874_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3873r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3874 :
    hubcapFit theRedpart rf8 p8_3873r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3874_1, c8_3874_2, c8_3874_3, c8_3874_4, c8_3874_5, c8_3874_6]

end FourColor

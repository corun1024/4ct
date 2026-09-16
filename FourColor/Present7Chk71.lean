import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 71 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3818l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3818l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3818l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3818l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3818l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3839_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3818l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3839 :
    hubcapFit theRedpart rf7 p7_3818l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3839_1, c7_3839_2, c7_3839_3, c7_3839_4, c7_3839_5, c7_3839_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3817l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3817l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3817l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3817l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3817l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3840_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3817l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3840 :
    hubcapFit theRedpart rf7 p7_3817l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3840_1, c7_3840_2, c7_3840_3, c7_3840_4, c7_3840_5, c7_3840_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3816l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3816l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3842_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3816l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3842 :
    hubcapFit theRedpart rf7 p7_3816l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3842_1, c7_3842_2, c7_3842_3, c7_3842_4, c7_3842_5, c7_3842_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3815l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3815l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3815l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3815l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3843_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3815l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3843 :
    hubcapFit theRedpart rf7 p7_3815l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3843_1, c7_3843_2, c7_3843_3, c7_3843_4, c7_3843_5, c7_3843_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3814l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3845_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3814l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3845 :
    hubcapFit theRedpart rf7 p7_3814l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3845_1, c7_3845_2, c7_3845_3, c7_3845_4, c7_3845_5, c7_3845_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3813l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3813l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3813l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3813l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3846_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3813l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3846 :
    hubcapFit theRedpart rf7 p7_3813l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3846_1, c7_3846_2, c7_3846_3, c7_3846_4, c7_3846_5, c7_3846_6, c7_3846_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3812l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3812l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3812l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3812l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3812l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3848_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3812l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3848 :
    hubcapFit theRedpart rf7 p7_3812l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3848_1, c7_3848_2, c7_3848_3, c7_3848_4, c7_3848_5, c7_3848_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3862r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3862r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3862r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3862r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3862r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3863_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3862r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3863 :
    hubcapFit theRedpart rf7 p7_3862r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3863_1, c7_3863_2, c7_3863_3, c7_3863_4, c7_3863_5, c7_3863_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3862l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3862l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3862l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3862l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3862l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3864_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3862l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3864 :
    hubcapFit theRedpart rf7 p7_3862l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3864_1, c7_3864_2, c7_3864_3, c7_3864_4, c7_3864_5, c7_3864_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3861l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3861l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3861l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3861l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3861l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3861l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3866_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3861l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3866 :
    hubcapFit theRedpart rf7 p7_3861l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3866_1, c7_3866_2, c7_3866_3, c7_3866_4, c7_3866_5, c7_3866_6, c7_3866_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3860l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3860l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3860l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3860l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3860l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3868_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3860l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3868 :
    hubcapFit theRedpart rf7 p7_3860l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3868_1, c7_3868_2, c7_3868_3, c7_3868_4, c7_3868_5, c7_3868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3859l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3859l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3859l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3859l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3859l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3869_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3859l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3869 :
    hubcapFit theRedpart rf7 p7_3859l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3869_1, c7_3869_2, c7_3869_3, c7_3869_4, c7_3869_5, c7_3869_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3858l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3858l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3871_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3858l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3871 :
    hubcapFit theRedpart rf7 p7_3858l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3871_1, c7_3871_2, c7_3871_3, c7_3871_4, c7_3871_5, c7_3871_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3856l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3856l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3856l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3873_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3856l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3873 :
    hubcapFit theRedpart rf7 p7_3856l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3873_1, c7_3873_2, c7_3873_3, c7_3873_4, c7_3873_5, c7_3873_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3874_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3855l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3874_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3855l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3874_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3855l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3874_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3855l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3874_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3855l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3874 :
    hubcapFit theRedpart rf7 p7_3855l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3874_1, c7_3874_2, c7_3874_3, c7_3874_4, c7_3874_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3854l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3854l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3876_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3854l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3876 :
    hubcapFit theRedpart rf7 p7_3854l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3876_1, c7_3876_2, c7_3876_3, c7_3876_4, c7_3876_5, c7_3876_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3877_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3877_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3877_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3853l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3877_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3853l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3877_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3853l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3877 :
    hubcapFit theRedpart rf7 p7_3853l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3877_1, c7_3877_2, c7_3877_3, c7_3877_4, c7_3877_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3879_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3879_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3879_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3852l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3879_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3852l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3879_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3852l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3879 :
    hubcapFit theRedpart rf7 p7_3852l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3879_1, c7_3879_2, c7_3879_3, c7_3879_4, c7_3879_5]

end FourColor

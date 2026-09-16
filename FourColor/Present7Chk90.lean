import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 90 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4800r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4800r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4800r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4800r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4800r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4800r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4801_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4800r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4801 :
    hubcapFit theRedpart rf7 p7_4800r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4801_1, c7_4801_2, c7_4801_3, c7_4801_4, c7_4801_5, c7_4801_6, c7_4801_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4800l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4800l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4800l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4802_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4800l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4802 :
    hubcapFit theRedpart rf7 p7_4800l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4802_1, c7_4802_2, c7_4802_3, c7_4802_4, c7_4802_5, c7_4802_6, c7_4802_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4799l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4799l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4799l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4799l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4799l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4804_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4799l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4804 :
    hubcapFit theRedpart rf7 p7_4799l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4804_1, c7_4804_2, c7_4804_3, c7_4804_4, c7_4804_5, c7_4804_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4798l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4798l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4798l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4798l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4798l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4805_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4798l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4805 :
    hubcapFit theRedpart rf7 p7_4798l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4805_1, c7_4805_2, c7_4805_3, c7_4805_4, c7_4805_5, c7_4805_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4797l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4797l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4797l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4797l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4797l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4807_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4797l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4807 :
    hubcapFit theRedpart rf7 p7_4797l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4807_1, c7_4807_2, c7_4807_3, c7_4807_4, c7_4807_5, c7_4807_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4796l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4796l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4796l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4796l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4796l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4796l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4808_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4796l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4808 :
    hubcapFit theRedpart rf7 p7_4796l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4808_1, c7_4808_2, c7_4808_3, c7_4808_4, c7_4808_5, c7_4808_6, c7_4808_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4794l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4794l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4794l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4794l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4794l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4810_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4794l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4810 :
    hubcapFit theRedpart rf7 p7_4794l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4810_1, c7_4810_2, c7_4810_3, c7_4810_4, c7_4810_5, c7_4810_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4793l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4793l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4793l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4793l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4793l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4812_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4793l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4812 :
    hubcapFit theRedpart rf7 p7_4793l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4812_1, c7_4812_2, c7_4812_3, c7_4812_4, c7_4812_5, c7_4812_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4826r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4826r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4827_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4826r) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4827 :
    hubcapFit theRedpart rf7 p7_4826r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4827_1, c7_4827_2, c7_4827_3, c7_4827_4, c7_4827_5, c7_4827_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4826l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4826l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4828_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4826l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4828 :
    hubcapFit theRedpart rf7 p7_4826l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4828_1, c7_4828_2, c7_4828_3, c7_4828_4, c7_4828_5, c7_4828_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4825l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4825l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4830_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4825l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4830 :
    hubcapFit theRedpart rf7 p7_4825l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4830_1, c7_4830_2, c7_4830_3, c7_4830_4, c7_4830_5, c7_4830_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4824l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4824l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4831_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4824l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4831 :
    hubcapFit theRedpart rf7 p7_4824l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4831_1, c7_4831_2, c7_4831_3, c7_4831_4, c7_4831_5, c7_4831_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4823l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4823l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4833_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4823l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4833 :
    hubcapFit theRedpart rf7 p7_4823l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4833_1, c7_4833_2, c7_4833_3, c7_4833_4, c7_4833_5, c7_4833_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4822l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4822l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4834_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4822l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4834 :
    hubcapFit theRedpart rf7 p7_4822l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4834_1, c7_4834_2, c7_4834_3, c7_4834_4, c7_4834_5, c7_4834_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4836_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4836_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4836_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4836_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4821l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4836_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4821l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4836 :
    hubcapFit theRedpart rf7 p7_4821l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4836_1, c7_4836_2, c7_4836_3, c7_4836_4, c7_4836_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4837_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4837_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4837_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4837_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4820l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4837_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4820l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4837 :
    hubcapFit theRedpart rf7 p7_4820l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4837_1, c7_4837_2, c7_4837_3, c7_4837_4, c7_4837_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4839_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4819l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4839_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4819l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4839_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4819l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4839_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4819l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4839_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4819l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4839 :
    hubcapFit theRedpart rf7 p7_4819l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4839_1, c7_4839_2, c7_4839_3, c7_4839_4, c7_4839_5]

end FourColor

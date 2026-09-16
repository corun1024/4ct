import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 15 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_822_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_803l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_822_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_803l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_822_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_803l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_822_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_803l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_822_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_803l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_822 :
    hubcapFit theRedpart rf7 p7_803l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_822_1, c7_822_2, c7_822_3, c7_822_4, c7_822_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_802l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_802l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_802l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_802l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_802l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_824_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_802l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_824 :
    hubcapFit theRedpart rf7 p7_802l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_824_1, c7_824_2, c7_824_3, c7_824_4, c7_824_5, c7_824_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_826_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_781l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_826_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_781l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_826_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_781l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_826_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_781l) (hubSubn 7 3 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_826_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_781l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_826 :
    hubcapFit theRedpart rf7 p7_781l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_826_1, c7_826_2, c7_826_3, c7_826_4, c7_826_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_780l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_780l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_780l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_827_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_780l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_827 :
    hubcapFit theRedpart rf7 p7_780l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_827_1, c7_827_2, c7_827_3, c7_827_4, c7_827_5, c7_827_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_829_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_779l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_829_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_779l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_829_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_829_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_779l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_829_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_779l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_829 :
    hubcapFit theRedpart rf7 p7_779l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_829_1, c7_829_2, c7_829_3, c7_829_4, c7_829_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_831_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_577l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_831_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_577l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_831_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_577l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_831_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_577l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_831_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_577l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_831 :
    hubcapFit theRedpart rf7 p7_577l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_831_1, c7_831_2, c7_831_3, c7_831_4, c7_831_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_833_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_833_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_833_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_576l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_833_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_576l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_833_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_576l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_833 :
    hubcapFit theRedpart rf7 p7_576l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_833_1, c7_833_2, c7_833_3, c7_833_4, c7_833_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_834_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_575l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_834_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_575l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_834_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_575l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_834_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_575l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_834_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_575l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_834 :
    hubcapFit theRedpart rf7 p7_575l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_834_1, c7_834_2, c7_834_3, c7_834_4, c7_834_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_836_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_574l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_836_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_574l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_836_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_574l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_836_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_574l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_836_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_574l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_836 :
    hubcapFit theRedpart rf7 p7_574l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_836_1, c7_836_2, c7_836_3, c7_836_4, c7_836_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_851_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_850r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_851_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_850r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_851_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_850r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_851_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_850r) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_851_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_850r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_851 :
    hubcapFit theRedpart rf7 p7_850r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_851_1, c7_851_2, c7_851_3, c7_851_4, c7_851_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_852_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_850l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_852_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_850l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_852_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_850l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_852_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_850l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_852_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_850l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_852 :
    hubcapFit theRedpart rf7 p7_850l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_852_1, c7_852_2, c7_852_3, c7_852_4, c7_852_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_854_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_849l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_854_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_849l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_854_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_849l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_854_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_849l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_854_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_849l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_854 :
    hubcapFit theRedpart rf7 p7_849l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_854_1, c7_854_2, c7_854_3, c7_854_4, c7_854_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_855_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_848l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_855_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_848l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_855_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_848l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_855_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_848l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_855_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_848l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_855 :
    hubcapFit theRedpart rf7 p7_848l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_855_1, c7_855_2, c7_855_3, c7_855_4, c7_855_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_857_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_847l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_857_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_847l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_857_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_847l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_857_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_847l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_857_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_847l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_857 :
    hubcapFit theRedpart rf7 p7_847l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_857_1, c7_857_2, c7_857_3, c7_857_4, c7_857_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_846l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_846l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_846l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_858_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_846l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_858 :
    hubcapFit theRedpart rf7 p7_846l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_858_1, c7_858_2, c7_858_3, c7_858_4, c7_858_5, c7_858_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_860_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_860_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_845l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_860_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_845l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_860_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_845l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_860 :
    hubcapFit theRedpart rf7 p7_845l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_860_1, c7_860_2, c7_860_3, c7_860_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_844l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_844l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_844l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_844l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_844l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_861_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_844l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_861 :
    hubcapFit theRedpart rf7 p7_844l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_861_1, c7_861_2, c7_861_3, c7_861_4, c7_861_5, c7_861_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_843l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_843l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_843l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_863_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_843l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_863 :
    hubcapFit theRedpart rf7 p7_843l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_863_1, c7_863_2, c7_863_3, c7_863_4, c7_863_5, c7_863_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_864_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_842l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_864 :
    hubcapFit theRedpart rf7 p7_842l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_864_1, c7_864_2, c7_864_3, c7_864_4, c7_864_5, c7_864_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_866_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_866_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_866_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_866_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_841l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_866_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_841l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_866 :
    hubcapFit theRedpart rf7 p7_841l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_866_1, c7_866_2, c7_866_3, c7_866_4, c7_866_5]

end FourColor

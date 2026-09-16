import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 15 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_758r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_758r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_758r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_758r) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_758r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_758r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_759_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_758r) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_759 :
    hubcapFit theRedpart rf8 p8_758r
    (Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_759_1, c8_759_2, c8_759_3, c8_759_4, c8_759_5, c8_759_6, c8_759_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_758l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_758l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_758l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_758l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_758l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_760_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_758l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_760 :
    hubcapFit theRedpart rf8 p8_758l
    (Hubcap.one 1 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_760_1, c8_760_2, c8_760_3, c8_760_4, c8_760_5, c8_760_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_757l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_757l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_762_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_762 :
    hubcapFit theRedpart rf8 p8_757l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_762_1, c8_762_2, c8_762_3, c8_762_4, c8_762_5, c8_762_6, c8_762_7, c8_762_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_764_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_756l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_764_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_756l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_764_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_756l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_764_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_756l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_764_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_756l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_764 :
    hubcapFit theRedpart rf8 p8_756l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_764_1, c8_764_2, c8_764_3, c8_764_4, c8_764_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_765_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_755l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_765_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_755l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_765_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_755l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_765_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_755l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_765_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_755l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_765 :
    hubcapFit theRedpart rf8 p8_755l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_765_1, c8_765_2, c8_765_3, c8_765_4, c8_765_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_772r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_772r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_772r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_772r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_772r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_772r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_773_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_772r) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_773 :
    hubcapFit theRedpart rf8 p8_772r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_773_1, c8_773_2, c8_773_3, c8_773_4, c8_773_5, c8_773_6, c8_773_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_772l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_772l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_772l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_772l) (hubSubn 8 7 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_774_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_772l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_774 :
    hubcapFit theRedpart rf8 p8_772l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_774_1, c8_774_2, c8_774_3, c8_774_4, c8_774_5, c8_774_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_771l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_771l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_771l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_771l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_771l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_776_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_771l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_776 :
    hubcapFit theRedpart rf8 p8_771l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_776_1, c8_776_2, c8_776_3, c8_776_4, c8_776_5, c8_776_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_770l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_770l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_770l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_770l) (hubSubn 8 7 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_777_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_770l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_777 :
    hubcapFit theRedpart rf8 p8_770l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_777_1, c8_777_2, c8_777_3, c8_777_4, c8_777_5, c8_777_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_769l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_769l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_769l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_769l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_779_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_769l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_779 :
    hubcapFit theRedpart rf8 p8_769l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_779_1, c8_779_2, c8_779_3, c8_779_4, c8_779_5, c8_779_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_786r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_786r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_786r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_786r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_786r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_786r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_787_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_786r) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_787 :
    hubcapFit theRedpart rf8 p8_786r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_787_1, c8_787_2, c8_787_3, c8_787_4, c8_787_5, c8_787_6, c8_787_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_786l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_786l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_786l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_788_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_786l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_788 :
    hubcapFit theRedpart rf8 p8_786l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_788_1, c8_788_2, c8_788_3, c8_788_4, c8_788_5, c8_788_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_785l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_785l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_785l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_785l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_785l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_790_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_785l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_790 :
    hubcapFit theRedpart rf8 p8_785l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_790_1, c8_790_2, c8_790_3, c8_790_4, c8_790_5, c8_790_6, c8_790_7, c8_790_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_792_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_792_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_792_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_784l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_792_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_784l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_792_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_784l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_792 :
    hubcapFit theRedpart rf8 p8_784l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_792_1, c8_792_2, c8_792_3, c8_792_4, c8_792_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_793_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_783l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_793_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_793_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_783l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_793_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_783l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_793_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_783l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_793 :
    hubcapFit theRedpart rf8 p8_783l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_793_1, c8_793_2, c8_793_3, c8_793_4, c8_793_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_799_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_798r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_799_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_798r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_799_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_798r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_799_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_798r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_799_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_798r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_799 :
    hubcapFit theRedpart rf8 p8_798r
    (Hubcap.one 0 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_799_1, c8_799_2, c8_799_3, c8_799_4, c8_799_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_798l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_798l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_798l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_798l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_798l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_800_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_798l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_800 :
    hubcapFit theRedpart rf8 p8_798l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_800_1, c8_800_2, c8_800_3, c8_800_4, c8_800_5, c8_800_6]

end FourColor

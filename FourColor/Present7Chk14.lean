import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 14 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_769_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_757l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_769_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_757l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_769_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_769_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_757l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_769_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_757l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_769 :
    hubcapFit theRedpart rf7 p7_757l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_769_1, c7_769_2, c7_769_3, c7_769_4, c7_769_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_646l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_646l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_646l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_646l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_772_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_646l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_772 :
    hubcapFit theRedpart rf7 p7_646l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_772_1, c7_772_2, c7_772_3, c7_772_4, c7_772_5, c7_772_6, c7_772_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_645l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_645l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_645l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_645l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_645l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_774_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_645l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_774 :
    hubcapFit theRedpart rf7 p7_645l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_774_1, c7_774_2, c7_774_3, c7_774_4, c7_774_5, c7_774_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_644l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_644l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_775_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_644l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_775 :
    hubcapFit theRedpart rf7 p7_644l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_775_1, c7_775_2, c7_775_3, c7_775_4, c7_775_5, c7_775_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_790r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_790r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_790r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_790r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_790r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_790r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_791_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_790r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_791 :
    hubcapFit theRedpart rf7 p7_790r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_791_1, c7_791_2, c7_791_3, c7_791_4, c7_791_5, c7_791_6, c7_791_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_790l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_790l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_790l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_790l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_790l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_792_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_790l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_792 :
    hubcapFit theRedpart rf7 p7_790l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_792_1, c7_792_2, c7_792_3, c7_792_4, c7_792_5, c7_792_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_788l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_788l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_788l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_788l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_788l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_788l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_794_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_788l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_794 :
    hubcapFit theRedpart rf7 p7_788l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_794_1, c7_794_2, c7_794_3, c7_794_4, c7_794_5, c7_794_6, c7_794_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_787l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_787l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_787l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_787l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_787l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_796_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_787l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_796 :
    hubcapFit theRedpart rf7 p7_787l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_796_1, c7_796_2, c7_796_3, c7_796_4, c7_796_5, c7_796_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_797_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_786l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_797_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_786l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_797_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_797_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_786l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_797_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_786l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_797 :
    hubcapFit theRedpart rf7 p7_786l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_797_1, c7_797_2, c7_797_3, c7_797_4, c7_797_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_799_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_785l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_799_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_785l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_799_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_785l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_799_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_785l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_799_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_785l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_799 :
    hubcapFit theRedpart rf7 p7_785l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_799_1, c7_799_2, c7_799_3, c7_799_4, c7_799_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_800_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_800_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_784l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_800_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_800_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_784l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_800_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_784l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_800 :
    hubcapFit theRedpart rf7 p7_784l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_800_1, c7_800_2, c7_800_3, c7_800_4, c7_800_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_810r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_810r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_810r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_810r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_810r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_811_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_810r) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_811 :
    hubcapFit theRedpart rf7 p7_810r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_811_1, c7_811_2, c7_811_3, c7_811_4, c7_811_5, c7_811_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_810l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_810l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_810l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_810l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_810l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_812_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_810l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_812 :
    hubcapFit theRedpart rf7 p7_810l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_812_1, c7_812_2, c7_812_3, c7_812_4, c7_812_5, c7_812_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_809l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_809l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_809l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_809l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_814_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_809l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_814 :
    hubcapFit theRedpart rf7 p7_809l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_814_1, c7_814_2, c7_814_3, c7_814_4, c7_814_5, c7_814_6, c7_814_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_816_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_808l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_816_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_816_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_816_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_808l) (hubSubn 7 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_816_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_808l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_816 :
    hubcapFit theRedpart rf7 p7_808l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 5 2 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_816_1, c7_816_2, c7_816_3, c7_816_4, c7_816_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_817_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_807l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_817_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_807l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_817_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_807l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_817_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_807l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_817_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_807l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_817 :
    hubcapFit theRedpart rf7 p7_807l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_817_1, c7_817_2, c7_817_3, c7_817_4, c7_817_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_819_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_806l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_819_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_806l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_819_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_806l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_819_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_806l) (hubSubn 7 3 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_819_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_806l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_819 :
    hubcapFit theRedpart rf7 p7_806l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 3 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_819_1, c7_819_2, c7_819_3, c7_819_4, c7_819_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_820_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_805l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_820_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_805l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_820_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_805l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_820_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_805l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_820_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_805l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_820 :
    hubcapFit theRedpart rf7 p7_805l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_820_1, c7_820_2, c7_820_3, c7_820_4, c7_820_5]

end FourColor

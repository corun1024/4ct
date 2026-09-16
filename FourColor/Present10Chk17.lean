import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 17 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_789l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_789l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_789l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_791_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_789l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_791 :
    hubcapFit theRedpart rf10 p10_789l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_791_1, c10_791_2, c10_791_3, c10_791_4, c10_791_5, c10_791_6, c10_791_7, c10_791_8, c10_791_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_787l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_787l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_787l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_793_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_787l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_793 :
    hubcapFit theRedpart rf10 p10_787l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_793_1, c10_793_2, c10_793_3, c10_793_4, c10_793_5, c10_793_6, c10_793_7, c10_793_8, c10_793_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_786l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_786l) (hubSubn 10 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_795_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_786l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_795 :
    hubcapFit theRedpart rf10 p10_786l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_795_1, c10_795_2, c10_795_3, c10_795_4, c10_795_5, c10_795_6, c10_795_7, c10_795_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_752l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_752l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_752l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_798_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_752l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_798 :
    hubcapFit theRedpart rf10 p10_752l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_798_1, c10_798_2, c10_798_3, c10_798_4, c10_798_5, c10_798_6, c10_798_7, c10_798_8, c10_798_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_751l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_751l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_751l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_751l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_800_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_751l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_800 :
    hubcapFit theRedpart rf10 p10_751l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_800_1, c10_800_2, c10_800_3, c10_800_4, c10_800_5, c10_800_6, c10_800_7, c10_800_8, c10_800_9, c10_800_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_749l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_749l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_749l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_802_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_749l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_802 :
    hubcapFit theRedpart rf10 p10_749l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_802_1, c10_802_2, c10_802_3, c10_802_4, c10_802_5, c10_802_6, c10_802_7, c10_802_8, c10_802_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_748l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_748l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_748l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_804_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_748l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_804 :
    hubcapFit theRedpart rf10 p10_748l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_804_1, c10_804_2, c10_804_3, c10_804_4, c10_804_5, c10_804_6, c10_804_7, c10_804_8, c10_804_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_747l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_747l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_747l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_806_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_747l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_806 :
    hubcapFit theRedpart rf10 p10_747l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_806_1, c10_806_2, c10_806_3, c10_806_4, c10_806_5, c10_806_6, c10_806_7, c10_806_8, c10_806_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_746l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_746l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_746l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_746l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_808_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_746l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_808 :
    hubcapFit theRedpart rf10 p10_746l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_808_1, c10_808_2, c10_808_3, c10_808_4, c10_808_5, c10_808_6, c10_808_7, c10_808_8, c10_808_9, c10_808_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_745l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_745l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_745l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_745l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_810_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_745l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_810 :
    hubcapFit theRedpart rf10 p10_745l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_810_1, c10_810_2, c10_810_3, c10_810_4, c10_810_5, c10_810_6, c10_810_7, c10_810_8, c10_810_9, c10_810_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_744l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_744l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_744l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_812_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_744l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_812 :
    hubcapFit theRedpart rf10 p10_744l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_812_1, c10_812_2, c10_812_3, c10_812_4, c10_812_5, c10_812_6, c10_812_7, c10_812_8, c10_812_9, c10_812_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_743l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_743l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_814_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_814 :
    hubcapFit theRedpart rf10 p10_743l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_814_1, c10_814_2, c10_814_3, c10_814_4, c10_814_5, c10_814_6, c10_814_7, c10_814_8, c10_814_9, c10_814_10]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 18 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_890l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_890l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_890l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_909_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_890l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_909 :
    hubcapFit theRedpart rf8 p8_890l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_909_1, c8_909_2, c8_909_3, c8_909_4, c8_909_5, c8_909_6, c8_909_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_918r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_918r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_918r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_918r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_918r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_919_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_918r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_919 :
    hubcapFit theRedpart rf8 p8_918r
    (Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_919_1, c8_919_2, c8_919_3, c8_919_4, c8_919_5, c8_919_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_920_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_918l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_920 :
    hubcapFit theRedpart rf8 p8_918l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_920_1, c8_920_2, c8_920_3, c8_920_4, c8_920_5, c8_920_6, c8_920_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_917l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_917l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_917l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_917l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_917l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_922_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_917l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_922 :
    hubcapFit theRedpart rf8 p8_917l
    (Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_922_1, c8_922_2, c8_922_3, c8_922_4, c8_922_5, c8_922_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_916l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_916l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_916l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_916l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_916l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_923_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_916l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_923 :
    hubcapFit theRedpart rf8 p8_916l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_923_1, c8_923_2, c8_923_3, c8_923_4, c8_923_5, c8_923_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_915l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_915l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_925_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_915l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_925 :
    hubcapFit theRedpart rf8 p8_915l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_925_1, c8_925_2, c8_925_3, c8_925_4, c8_925_5, c8_925_6, c8_925_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_914l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_914l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_927_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_914l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_927 :
    hubcapFit theRedpart rf8 p8_914l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_927_1, c8_927_2, c8_927_3, c8_927_4, c8_927_5, c8_927_6, c8_927_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_913l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_913l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_913l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_929_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_913l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_929 :
    hubcapFit theRedpart rf8 p8_913l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_929_1, c8_929_2, c8_929_3, c8_929_4, c8_929_5, c8_929_6, c8_929_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_912l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_912l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_912l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_912l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_931_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_912l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_931 :
    hubcapFit theRedpart rf8 p8_912l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_931_1, c8_931_2, c8_931_3, c8_931_4, c8_931_5, c8_931_6, c8_931_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_911l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_911l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_911l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_911l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_933_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_911l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_933 :
    hubcapFit theRedpart rf8 p8_911l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_933_1, c8_933_2, c8_933_3, c8_933_4, c8_933_5, c8_933_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_941r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_941r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_941r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_941r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_941r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_942_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_941r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_942 :
    hubcapFit theRedpart rf8 p8_941r
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_942_1, c8_942_2, c8_942_3, c8_942_4, c8_942_5, c8_942_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_940l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_940l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_943_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_940l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_943 :
    hubcapFit theRedpart rf8 p8_940l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_943_1, c8_943_2, c8_943_3, c8_943_4, c8_943_5, c8_943_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_939l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_939l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_939l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_939l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_945_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_939l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_945 :
    hubcapFit theRedpart rf8 p8_939l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_945_1, c8_945_2, c8_945_3, c8_945_4, c8_945_5, c8_945_6, c8_945_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_938l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_947_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_938l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_947 :
    hubcapFit theRedpart rf8 p8_938l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_947_1, c8_947_2, c8_947_3, c8_947_4, c8_947_5, c8_947_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_937l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_937l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_937l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_948_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_937l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_948 :
    hubcapFit theRedpart rf8 p8_937l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_948_1, c8_948_2, c8_948_3, c8_948_4, c8_948_5, c8_948_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_950_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_950_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_936l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_950_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_936l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_950_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_936l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_950_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_936l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_950 :
    hubcapFit theRedpart rf8 p8_936l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_950_1, c8_950_2, c8_950_3, c8_950_4, c8_950_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_935l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_935l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_935l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_951_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_935l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_951 :
    hubcapFit theRedpart rf8 p8_935l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_951_1, c8_951_2, c8_951_3, c8_951_4, c8_951_5, c8_951_6]

end FourColor

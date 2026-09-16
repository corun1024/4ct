import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 21 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_963l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_963l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_963l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_977_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_963l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_977 :
    hubcapFit theRedpart rf9 p9_963l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_977_1, c9_977_2, c9_977_3, c9_977_4, c9_977_5, c9_977_6, c9_977_7, c9_977_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_962l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_979_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_962l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_979 :
    hubcapFit theRedpart rf9 p9_962l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_979_1, c9_979_2, c9_979_3, c9_979_4, c9_979_5, c9_979_6, c9_979_7, c9_979_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_960l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_960l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_960l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_960l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_981_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_960l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_981 :
    hubcapFit theRedpart rf9 p9_960l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_981_1, c9_981_2, c9_981_3, c9_981_4, c9_981_5, c9_981_6, c9_981_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_959l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_959l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_983_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_959l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_983 :
    hubcapFit theRedpart rf9 p9_959l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_983_1, c9_983_2, c9_983_3, c9_983_4, c9_983_5, c9_983_6, c9_983_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_958l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_958l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_958l) (hubSubn 9 7 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_985_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_958l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_985 :
    hubcapFit theRedpart rf9 p9_958l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_985_1, c9_985_2, c9_985_3, c9_985_4, c9_985_5, c9_985_6, c9_985_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_987l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_987l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_987l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_987l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_987l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_987l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_988_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_987l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_988 :
    hubcapFit theRedpart rf9 p9_987l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_988_1, c9_988_2, c9_988_3, c9_988_4, c9_988_5, c9_988_6, c9_988_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_990l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_990l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_990l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_990l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_990l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_990l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_991_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_990l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_991 :
    hubcapFit theRedpart rf9 p9_990l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_991_1, c9_991_2, c9_991_3, c9_991_4, c9_991_5, c9_991_6, c9_991_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_990r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_990r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_990r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_990r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_990r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_990r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_993_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_990r) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_993 :
    hubcapFit theRedpart rf9 p9_990r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_993_1, c9_993_2, c9_993_3, c9_993_4, c9_993_5, c9_993_6, c9_993_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1000r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1000r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1000r) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1000r) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1001_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1000r) (hubSubn 9 7 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1001 :
    hubcapFit theRedpart rf9 p9_1000r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1001_1, c9_1001_2, c9_1001_3, c9_1001_4, c9_1001_5, c9_1001_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1000l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1002_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1000l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1002 :
    hubcapFit theRedpart rf9 p9_1000l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1002_1, c9_1002_2, c9_1002_3, c9_1002_4, c9_1002_5, c9_1002_6, c9_1002_7, c9_1002_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_999l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_999l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1004_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_999l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1004 :
    hubcapFit theRedpart rf9 p9_999l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1004_1, c9_1004_2, c9_1004_3, c9_1004_4, c9_1004_5, c9_1004_6, c9_1004_7, c9_1004_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_998l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1006_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_998l) (hubSubn 9 5 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1006 :
    hubcapFit theRedpart rf9 p9_998l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1006_1, c9_1006_2, c9_1006_3, c9_1006_4, c9_1006_5, c9_1006_6, c9_1006_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_925l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_925l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_925l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_925l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_925l) (hubSubn 9 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1008_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_925l) (hubSubn 9 5 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1008 :
    hubcapFit theRedpart rf9 p9_925l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1008_1, c9_1008_2, c9_1008_3, c9_1008_4, c9_1008_5, c9_1008_6, c9_1008_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_924l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_924l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_924l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_924l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1010_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_924l) (hubSubn 9 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1010 :
    hubcapFit theRedpart rf9 p9_924l
    (Hubcap.one 2 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1010_1, c9_1010_2, c9_1010_3, c9_1010_4, c9_1010_5, c9_1010_6, c9_1010_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_923l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_923l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_923l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_923l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_923l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1012_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_923l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1012 :
    hubcapFit theRedpart rf9 p9_923l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1012_1, c9_1012_2, c9_1012_3, c9_1012_4, c9_1012_5, c9_1012_6]

end FourColor

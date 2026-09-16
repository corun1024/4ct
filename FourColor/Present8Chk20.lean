import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 20 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1007r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1007r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1007r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1008_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1007r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1008 :
    hubcapFit theRedpart rf8 p8_1007r
    (Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1008_1, c8_1008_2, c8_1008_3, c8_1008_4, c8_1008_5, c8_1008_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1007l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1009_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1007l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1009 :
    hubcapFit theRedpart rf8 p8_1007l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1009_1, c8_1009_2, c8_1009_3, c8_1009_4, c8_1009_5, c8_1009_6, c8_1009_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1006l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1011_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1006l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1011 :
    hubcapFit theRedpart rf8 p8_1006l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1011_1, c8_1011_2, c8_1011_3, c8_1011_4, c8_1011_5, c8_1011_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1014r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1014r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1014r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1014r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1014r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1015_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1014r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1015 :
    hubcapFit theRedpart rf8 p8_1014r
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1015_1, c8_1015_2, c8_1015_3, c8_1015_4, c8_1015_5, c8_1015_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1014l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1014l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1014l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1014l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1016_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1014l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1016 :
    hubcapFit theRedpart rf8 p8_1014l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1016_1, c8_1016_2, c8_1016_3, c8_1016_4, c8_1016_5, c8_1016_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1013l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1013l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1013l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1013l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1013l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1013l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1018_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1013l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1018 :
    hubcapFit theRedpart rf8 p8_1013l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1018_1, c8_1018_2, c8_1018_3, c8_1018_4, c8_1018_5, c8_1018_6, c8_1018_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1003l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1003l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1003l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1003l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1003l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1020_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1003l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1020 :
    hubcapFit theRedpart rf8 p8_1003l
    (Hubcap.one 6 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1020_1, c8_1020_2, c8_1020_3, c8_1020_4, c8_1020_5, c8_1020_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1024r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1024r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1024r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1024r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1024r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1025_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1024r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1025 :
    hubcapFit theRedpart rf8 p8_1024r
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1025_1, c8_1025_2, c8_1025_3, c8_1025_4, c8_1025_5, c8_1025_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1024l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1026_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1024l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1026 :
    hubcapFit theRedpart rf8 p8_1024l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1026_1, c8_1026_2, c8_1026_3, c8_1026_4, c8_1026_5, c8_1026_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1023l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1023l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1023l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1028_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1023l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1028 :
    hubcapFit theRedpart rf8 p8_1023l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1028_1, c8_1028_2, c8_1028_3, c8_1028_4, c8_1028_5, c8_1028_6, c8_1028_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1022l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1030_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1022l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1030 :
    hubcapFit theRedpart rf8 p8_1022l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1030_1, c8_1030_2, c8_1030_3, c8_1030_4, c8_1030_5, c8_1030_6, c8_1030_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1032_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1032_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1032_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1001l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1032_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1001l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1032_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1001l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1032 :
    hubcapFit theRedpart rf8 p8_1001l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1032_1, c8_1032_2, c8_1032_3, c8_1032_4, c8_1032_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1034_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1034_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1034_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1000l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1034_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1000l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1034_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1000l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1034 :
    hubcapFit theRedpart rf8 p8_1000l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1034_1, c8_1034_2, c8_1034_3, c8_1034_4, c8_1034_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_979l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_979l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_979l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_979l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_979l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1036_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_979l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1036 :
    hubcapFit theRedpart rf8 p8_979l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1036_1, c8_1036_2, c8_1036_3, c8_1036_4, c8_1036_5, c8_1036_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_978l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_978l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_978l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_978l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1037_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_978l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1037 :
    hubcapFit theRedpart rf8 p8_978l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1037_1, c8_1037_2, c8_1037_3, c8_1037_4, c8_1037_5, c8_1037_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_739l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_739l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_739l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_739l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1040_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_739l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1040 :
    hubcapFit theRedpart rf8 p8_739l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1040_1, c8_1040_2, c8_1040_3, c8_1040_4, c8_1040_5, c8_1040_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_738l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_738l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_738l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1041_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_738l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1041 :
    hubcapFit theRedpart rf8 p8_738l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1041_1, c8_1041_2, c8_1041_3, c8_1041_4, c8_1041_5, c8_1041_6]

end FourColor

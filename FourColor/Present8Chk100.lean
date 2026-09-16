import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 100 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4938l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4938l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4978_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4978 :
    hubcapFit theRedpart rf8 p8_4938l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4978_1, c8_4978_2, c8_4978_3, c8_4978_4, c8_4978_5, c8_4978_6, c8_4978_7, c8_4978_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4937l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4937l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4937l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4937l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4980_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4937l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4980 :
    hubcapFit theRedpart rf8 p8_4937l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4980_1, c8_4980_2, c8_4980_3, c8_4980_4, c8_4980_5, c8_4980_6, c8_4980_7, c8_4980_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4936l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4936l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4936l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4936l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4982_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4936l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4982 :
    hubcapFit theRedpart rf8 p8_4936l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4982_1, c8_4982_2, c8_4982_3, c8_4982_4, c8_4982_5, c8_4982_6, c8_4982_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4991r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4991r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4991r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4991r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4991r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4991r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4992_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4991r) (hubSubn 8 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4992 :
    hubcapFit theRedpart rf8 p8_4991r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4992_1, c8_4992_2, c8_4992_3, c8_4992_4, c8_4992_5, c8_4992_6, c8_4992_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4999l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4999l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4999l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5000_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4999l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5000 :
    hubcapFit theRedpart rf8 p8_4999l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5000_1, c8_5000_2, c8_5000_3, c8_5000_4, c8_5000_5, c8_5000_6, c8_5000_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4999r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4999r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4999r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4999r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4999r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4999r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5002_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4999r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5002 :
    hubcapFit theRedpart rf8 p8_4999r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5002_1, c8_5002_2, c8_5002_3, c8_5002_4, c8_5002_5, c8_5002_6, c8_5002_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4998l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5005_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4998l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5005 :
    hubcapFit theRedpart rf8 p8_4998l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5005_1, c8_5005_2, c8_5005_3, c8_5005_4, c8_5005_5, c8_5005_6, c8_5005_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5007l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5007l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5008_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5007l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5008 :
    hubcapFit theRedpart rf8 p8_5007l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5008_1, c8_5008_2, c8_5008_3, c8_5008_4, c8_5008_5, c8_5008_6, c8_5008_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5007r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5007r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5007r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5010_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5007r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5010 :
    hubcapFit theRedpart rf8 p8_5007r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5010_1, c8_5010_2, c8_5010_3, c8_5010_4, c8_5010_5, c8_5010_6, c8_5010_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4996l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4996l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5013_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5013 :
    hubcapFit theRedpart rf8 p8_4996l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5013_1, c8_5013_2, c8_5013_3, c8_5013_4, c8_5013_5, c8_5013_6, c8_5013_7, c8_5013_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4995l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4995l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4995l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4995l) (hubSubn 8 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5015_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4995l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5015 :
    hubcapFit theRedpart rf8 p8_4995l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5015_1, c8_5015_2, c8_5015_3, c8_5015_4, c8_5015_5, c8_5015_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5023r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5023r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5023r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5023r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5023r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5023r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5023r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5024_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5023r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5024 :
    hubcapFit theRedpart rf8 p8_5023r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5024_1, c8_5024_2, c8_5024_3, c8_5024_4, c8_5024_5, c8_5024_6, c8_5024_7, c8_5024_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5023l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5023l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5025_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5025 :
    hubcapFit theRedpart rf8 p8_5023l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5025_1, c8_5025_2, c8_5025_3, c8_5025_4, c8_5025_5, c8_5025_6, c8_5025_7, c8_5025_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5022l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5022l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5022l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5027_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5027 :
    hubcapFit theRedpart rf8 p8_5022l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5027_1, c8_5027_2, c8_5027_3, c8_5027_4, c8_5027_5, c8_5027_6, c8_5027_7, c8_5027_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5021l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5021l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5021l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5021l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5021l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5021l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5029_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5021l) (hubSubn 8 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5029 :
    hubcapFit theRedpart rf8 p8_5021l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5029_1, c8_5029_2, c8_5029_3, c8_5029_4, c8_5029_5, c8_5029_6, c8_5029_7]

end FourColor

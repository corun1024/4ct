import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 110 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5857l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5857l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5857l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5857l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5857l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5857l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5859_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5857l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5859 :
    hubcapFit theRedpart rf7 p7_5857l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5859_1, c7_5859_2, c7_5859_3, c7_5859_4, c7_5859_5, c7_5859_6, c7_5859_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5856l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5856l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5856l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5856l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5856l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5861_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5856l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5861 :
    hubcapFit theRedpart rf7 p7_5856l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5861_1, c7_5861_2, c7_5861_3, c7_5861_4, c7_5861_5, c7_5861_6, c7_5861_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5865r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5865r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5865r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5865r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5865r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5865r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5866_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5865r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5866 :
    hubcapFit theRedpart rf7 p7_5865r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5866_1, c7_5866_2, c7_5866_3, c7_5866_4, c7_5866_5, c7_5866_6, c7_5866_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5865l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5865l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5865l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5865l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5867_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5865l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5867 :
    hubcapFit theRedpart rf7 p7_5865l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5867_1, c7_5867_2, c7_5867_3, c7_5867_4, c7_5867_5, c7_5867_6, c7_5867_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5864l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5864l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5864l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5864l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5864l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5864l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5869_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5864l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5869 :
    hubcapFit theRedpart rf7 p7_5864l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5869_1, c7_5869_2, c7_5869_3, c7_5869_4, c7_5869_5, c7_5869_6, c7_5869_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5872r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5872r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5872r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5872r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5872r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5872r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5873_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5872r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5873 :
    hubcapFit theRedpart rf7 p7_5872r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5873_1, c7_5873_2, c7_5873_3, c7_5873_4, c7_5873_5, c7_5873_6, c7_5873_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5872l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5872l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5872l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5872l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5872l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5872l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5874_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5872l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5874 :
    hubcapFit theRedpart rf7 p7_5872l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5874_1, c7_5874_2, c7_5874_3, c7_5874_4, c7_5874_5, c7_5874_6, c7_5874_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5871l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5871l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5871l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5871l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5871l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5871l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5876_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5871l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5876 :
    hubcapFit theRedpart rf7 p7_5871l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5876_1, c7_5876_2, c7_5876_3, c7_5876_4, c7_5876_5, c7_5876_6, c7_5876_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5837l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5837l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5837l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5837l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5837l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5879_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5837l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5879 :
    hubcapFit theRedpart rf7 p7_5837l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5879_1, c7_5879_2, c7_5879_3, c7_5879_4, c7_5879_5, c7_5879_6, c7_5879_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5836l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5836l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5836l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5836l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5836l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5836l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5881_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5836l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5881 :
    hubcapFit theRedpart rf7 p7_5836l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5881_1, c7_5881_2, c7_5881_3, c7_5881_4, c7_5881_5, c7_5881_6, c7_5881_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5887r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5887r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5887r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5887r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5887r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5887r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5888_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5887r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5888 :
    hubcapFit theRedpart rf7 p7_5887r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5888_1, c7_5888_2, c7_5888_3, c7_5888_4, c7_5888_5, c7_5888_6, c7_5888_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5887l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5887l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5887l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5887l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5887l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5887l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5889_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5887l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5889 :
    hubcapFit theRedpart rf7 p7_5887l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5889_1, c7_5889_2, c7_5889_3, c7_5889_4, c7_5889_5, c7_5889_6, c7_5889_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5885l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5885l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5885l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5885l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5891_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5885l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5891 :
    hubcapFit theRedpart rf7 p7_5885l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5891_1, c7_5891_2, c7_5891_3, c7_5891_4, c7_5891_5, c7_5891_6, c7_5891_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5884l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5884l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5884l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5884l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5884l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5884l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5893_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5884l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5893 :
    hubcapFit theRedpart rf7 p7_5884l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5893_1, c7_5893_2, c7_5893_3, c7_5893_4, c7_5893_5, c7_5893_6, c7_5893_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5883l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5883l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5883l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5883l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5883l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5883l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5895_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5883l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5895 :
    hubcapFit theRedpart rf7 p7_5883l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5895_1, c7_5895_2, c7_5895_3, c7_5895_4, c7_5895_5, c7_5895_6, c7_5895_7]

end FourColor

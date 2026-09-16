import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 105 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5569l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5574_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5569l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5574 :
    hubcapFit theRedpart rf7 p7_5569l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5574_1, c7_5574_2, c7_5574_3, c7_5574_4, c7_5574_5, c7_5574_6, c7_5574_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5568l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5568l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5576_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5568l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5576 :
    hubcapFit theRedpart rf7 p7_5568l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5576_1, c7_5576_2, c7_5576_3, c7_5576_4, c7_5576_5, c7_5576_6, c7_5576_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5567l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5567l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5567l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5567l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5567l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5578_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5578 :
    hubcapFit theRedpart rf7 p7_5567l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5578_1, c7_5578_2, c7_5578_3, c7_5578_4, c7_5578_5, c7_5578_6, c7_5578_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5566l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5566l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5580_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5566l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5580 :
    hubcapFit theRedpart rf7 p7_5566l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5580_1, c7_5580_2, c7_5580_3, c7_5580_4, c7_5580_5, c7_5580_6, c7_5580_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5565l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5565l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5565l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5565l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5565l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5565l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5582_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5565l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5582 :
    hubcapFit theRedpart rf7 p7_5565l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5582_1, c7_5582_2, c7_5582_3, c7_5582_4, c7_5582_5, c7_5582_6, c7_5582_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5564l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5584_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5564l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5584 :
    hubcapFit theRedpart rf7 p7_5564l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5584_1, c7_5584_2, c7_5584_3, c7_5584_4, c7_5584_5, c7_5584_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5562l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5562l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5562l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5586_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5562l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5586 :
    hubcapFit theRedpart rf7 p7_5562l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5586_1, c7_5586_2, c7_5586_3, c7_5586_4, c7_5586_5, c7_5586_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5595r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5595r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5595r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5595r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5595r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5596_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5595r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5596 :
    hubcapFit theRedpart rf7 p7_5595r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5596_1, c7_5596_2, c7_5596_3, c7_5596_4, c7_5596_5, c7_5596_6, c7_5596_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5595l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5595l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5597_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5595l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5597 :
    hubcapFit theRedpart rf7 p7_5595l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5597_1, c7_5597_2, c7_5597_3, c7_5597_4, c7_5597_5, c7_5597_6, c7_5597_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5594l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5594l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5599_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5594l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5599 :
    hubcapFit theRedpart rf7 p7_5594l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5599_1, c7_5599_2, c7_5599_3, c7_5599_4, c7_5599_5, c7_5599_6, c7_5599_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5602r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5602r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5602r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5602r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5602r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5602r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5603_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5602r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5603 :
    hubcapFit theRedpart rf7 p7_5602r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5603_1, c7_5603_2, c7_5603_3, c7_5603_4, c7_5603_5, c7_5603_6, c7_5603_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5602l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5602l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5604_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5602l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5604 :
    hubcapFit theRedpart rf7 p7_5602l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5604_1, c7_5604_2, c7_5604_3, c7_5604_4, c7_5604_5, c7_5604_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5601l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5601l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5601l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5606_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5601l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5606 :
    hubcapFit theRedpart rf7 p7_5601l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5606_1, c7_5606_2, c7_5606_3, c7_5606_4, c7_5606_5, c7_5606_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5591l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5591l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5591l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5608_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5591l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5608 :
    hubcapFit theRedpart rf7 p7_5591l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5608_1, c7_5608_2, c7_5608_3, c7_5608_4, c7_5608_5, c7_5608_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5613r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5613r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5613r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5613r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5613r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5613r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5614_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5613r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5614 :
    hubcapFit theRedpart rf7 p7_5613r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5614_1, c7_5614_2, c7_5614_3, c7_5614_4, c7_5614_5, c7_5614_6, c7_5614_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5613l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5613l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5613l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5613l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5613l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5615_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5613l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5615 :
    hubcapFit theRedpart rf7 p7_5613l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5615_1, c7_5615_2, c7_5615_3, c7_5615_4, c7_5615_5, c7_5615_6, c7_5615_7]

end FourColor

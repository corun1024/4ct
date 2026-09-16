import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 79 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4132l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4132l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4132l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4223_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4132l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4223 :
    hubcapFit theRedpart rf7 p7_4132l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4223_1, c7_4223_2, c7_4223_3, c7_4223_4, c7_4223_5, c7_4223_6, c7_4223_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4236r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4236r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4236r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4236r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4236r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4236r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4237_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4236r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4237 :
    hubcapFit theRedpart rf7 p7_4236r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4237_1, c7_4237_2, c7_4237_3, c7_4237_4, c7_4237_5, c7_4237_6, c7_4237_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4236l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4236l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4236l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4236l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4238_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4236l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4238 :
    hubcapFit theRedpart rf7 p7_4236l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4238_1, c7_4238_2, c7_4238_3, c7_4238_4, c7_4238_5, c7_4238_6, c7_4238_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4235l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4235l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4235l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4235l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4235l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4235l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4240_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4235l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4240 :
    hubcapFit theRedpart rf7 p7_4235l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4240_1, c7_4240_2, c7_4240_3, c7_4240_4, c7_4240_5, c7_4240_6, c7_4240_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4246r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4246r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4246r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4246r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4246r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4246r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4247_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4246r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4247 :
    hubcapFit theRedpart rf7 p7_4246r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4247_1, c7_4247_2, c7_4247_3, c7_4247_4, c7_4247_5, c7_4247_6, c7_4247_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4246l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4246l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4246l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4246l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4248_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4248 :
    hubcapFit theRedpart rf7 p7_4246l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4248_1, c7_4248_2, c7_4248_3, c7_4248_4, c7_4248_5, c7_4248_6, c7_4248_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4245l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4245l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4245l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4245l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4245l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4250_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4245l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4250 :
    hubcapFit theRedpart rf7 p7_4245l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4250_1, c7_4250_2, c7_4250_3, c7_4250_4, c7_4250_5, c7_4250_6, c7_4250_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4244l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4244l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4244l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4244l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4244l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4244l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4252_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4244l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4252 :
    hubcapFit theRedpart rf7 p7_4244l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4252_1, c7_4252_2, c7_4252_3, c7_4252_4, c7_4252_5, c7_4252_6, c7_4252_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4242l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4242l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4242l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4254_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4242l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4254 :
    hubcapFit theRedpart rf7 p7_4242l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4254_1, c7_4254_2, c7_4254_3, c7_4254_4, c7_4254_5, c7_4254_6, c7_4254_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4263r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4263r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4263r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4263r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4263r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4263r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4264_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4263r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4264 :
    hubcapFit theRedpart rf7 p7_4263r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4264_1, c7_4264_2, c7_4264_3, c7_4264_4, c7_4264_5, c7_4264_6, c7_4264_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4263l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4263l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4263l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4263l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4265_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4263l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4265 :
    hubcapFit theRedpart rf7 p7_4263l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4265_1, c7_4265_2, c7_4265_3, c7_4265_4, c7_4265_5, c7_4265_6, c7_4265_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4262l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4262l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4262l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4262l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4262l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4262l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4267_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4262l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4267 :
    hubcapFit theRedpart rf7 p7_4262l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4267_1, c7_4267_2, c7_4267_3, c7_4267_4, c7_4267_5, c7_4267_6, c7_4267_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4261l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4269_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4261l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4269 :
    hubcapFit theRedpart rf7 p7_4261l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4269_1, c7_4269_2, c7_4269_3, c7_4269_4, c7_4269_5, c7_4269_6, c7_4269_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4278r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4278r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4278r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4278r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4278r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4279_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4278r) (hubSubn 7 6 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4279 :
    hubcapFit theRedpart rf7 p7_4278r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4279_1, c7_4279_2, c7_4279_3, c7_4279_4, c7_4279_5, c7_4279_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4285r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4285r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4285r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4285r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4285r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4285r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4286_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4285r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4286 :
    hubcapFit theRedpart rf7 p7_4285r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4286_1, c7_4286_2, c7_4286_3, c7_4286_4, c7_4286_5, c7_4286_6, c7_4286_7]

end FourColor

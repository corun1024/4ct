import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_480_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_479r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_480_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_479r) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_480_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_479r) (hubSubn 6 5 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_480 :
    hubcapFit theRedpart rf6 p6_479r
    (Hubcap.two 2 4 1 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 0 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_480_1, c6_480_2, c6_480_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_481_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_479l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_481_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_479l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_481_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_479l) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_481 :
    hubcapFit theRedpart rf6 p6_479l
    (Hubcap.two 2 4 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 0 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_481_1, c6_481_2, c6_481_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_499_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_498r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_499_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_498r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_499_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_498r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_499 :
    hubcapFit theRedpart rf6 p6_498r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_499_1, c6_499_2, c6_499_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_500_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_497l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_500_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_497l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_500_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_497l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_500 :
    hubcapFit theRedpart rf6 p6_497l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_500_1, c6_500_2, c6_500_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_504_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_503r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_504_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_503r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_504_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_503r) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_504 :
    hubcapFit theRedpart rf6 p6_503r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_504_1, c6_504_2, c6_504_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_505_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_503l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_505_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_503l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_505_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_503l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_505 :
    hubcapFit theRedpart rf6 p6_503l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_505_1, c6_505_2, c6_505_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_507_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_502l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_507_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_502l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_507_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_502l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_507 :
    hubcapFit theRedpart rf6 p6_502l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_507_1, c6_507_2, c6_507_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_510_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_509r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_510_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_509r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_510_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_509r) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_510 :
    hubcapFit theRedpart rf6 p6_509r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_510_1, c6_510_2, c6_510_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_511_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_509l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_511_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_509l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_511_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_509l) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_511 :
    hubcapFit theRedpart rf6 p6_509l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_511_1, c6_511_2, c6_511_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_515_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_514r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_515_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_514r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_515_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_514r) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_515 :
    hubcapFit theRedpart rf6 p6_514r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_515_1, c6_515_2, c6_515_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_516_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_513l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_516_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_513l) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_516_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_513l) (hubSubn 6 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_516 :
    hubcapFit theRedpart rf6 p6_513l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_516_1, c6_516_2, c6_516_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_518_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_491l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_518_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_491l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_518_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_491l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_518 :
    hubcapFit theRedpart rf6 p6_491l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_518_1, c6_518_2, c6_518_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_527_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_526r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_527_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_526r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_527_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_526r) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_527 :
    hubcapFit theRedpart rf6 p6_526r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_527_1, c6_527_2, c6_527_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_528_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_526l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_528_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_526l) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_528_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_526l) (hubSubn 6 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_528 :
    hubcapFit theRedpart rf6 p6_526l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_528_1, c6_528_2, c6_528_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_530_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_525l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_530_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_525l) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_530_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_525l) (hubSubn 6 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_530 :
    hubcapFit theRedpart rf6 p6_525l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_530_1, c6_530_2, c6_530_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_532_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_531r) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_532_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_531r) (hubSubn 6 5 3) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_532_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_531r) (hubSubn 6 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_532 :
    hubcapFit theRedpart rf6 p6_531r
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_532_1, c6_532_2, c6_532_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_533_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_531l) (hubSubn 6 4 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_533_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_531l) (hubSubn 6 5 3) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_533_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_531l) (hubSubn 6 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_533 :
    hubcapFit theRedpart rf6 p6_531l
    (Hubcap.two 0 4 (-3) <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_533_1, c6_533_2, c6_533_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_538_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_537r) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_538_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_537r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_538_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_537r) (hubSubn 6 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_538 :
    hubcapFit theRedpart rf6 p6_537r
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_538_1, c6_538_2, c6_538_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_539_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_537l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_539_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_537l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_539_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_537l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_539 :
    hubcapFit theRedpart rf6 p6_537l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_539_1, c6_539_2, c6_539_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_541_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_536l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_541_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_536l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_541_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_536l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_541 :
    hubcapFit theRedpart rf6 p6_536l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_541_1, c6_541_2, c6_541_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_543_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_542r) (hubSubn 6 2 0) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_543_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_542r) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_543_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_542r) (hubSubn 6 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_543 :
    hubcapFit theRedpart rf6 p6_542r
    (Hubcap.two 0 2 (-4) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_543_1, c6_543_2, c6_543_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_544_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_542l) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_544_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_542l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_544_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_542l) (hubSubn 6 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_544 :
    hubcapFit theRedpart rf6 p6_542l
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_544_1, c6_544_2, c6_544_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_550_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_549r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_550_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_549r) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_550_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_549r) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_550 :
    hubcapFit theRedpart rf6 p6_549r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_550_1, c6_550_2, c6_550_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_552_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_551r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_552_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_551r) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_552_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_551r) (hubSubn 6 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_552 :
    hubcapFit theRedpart rf6 p6_551r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_552_1, c6_552_2, c6_552_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_553_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_551l) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_553_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_551l) (hubSubn 6 3 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_553_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_551l) (hubSubn 6 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_553 :
    hubcapFit theRedpart rf6 p6_551l
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_553_1, c6_553_2, c6_553_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_556_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_555r) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_556_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_555r) (hubSubn 6 3 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_556_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_555r) (hubSubn 6 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_556 :
    hubcapFit theRedpart rf6 p6_555r
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_556_1, c6_556_2, c6_556_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_557_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_555l) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_557_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_555l) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_557_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_555l) (hubSubn 6 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_557 :
    hubcapFit theRedpart rf6 p6_555l
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_557_1, c6_557_2, c6_557_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_560_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_559r) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_560_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_559r) (hubSubn 6 3 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_560_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_559r) (hubSubn 6 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_560 :
    hubcapFit theRedpart rf6 p6_559r
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_560_1, c6_560_2, c6_560_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_561_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_559l) (hubSubn 6 2 0) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_561_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_559l) (hubSubn 6 3 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_561_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_559l) (hubSubn 6 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_561 :
    hubcapFit theRedpart rf6 p6_559l
    (Hubcap.two 0 2 (-4) <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_561_1, c6_561_2, c6_561_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_567_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_566r) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_567_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_566r) (hubSubn 6 5 3) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_567_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_566r) (hubSubn 6 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_567 :
    hubcapFit theRedpart rf6 p6_566r
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_567_1, c6_567_2, c6_567_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_568_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_566l) (hubSubn 6 4 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_568_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_566l) (hubSubn 6 5 3) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_568_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_566l) (hubSubn 6 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_568 :
    hubcapFit theRedpart rf6 p6_566l
    (Hubcap.two 0 4 (-3) <|
     Hubcap.two 3 5 (-3) <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_568_1, c6_568_2, c6_568_3]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 10 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_494l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_494l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_494l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_494l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_494l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_503_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_494l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_503 :
    hubcapFit theRedpart rf8 p8_494l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_503_1, c8_503_2, c8_503_3, c8_503_4, c8_503_5, c8_503_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_505_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_492l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_505_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_505_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_492l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_505_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_492l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_505_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_492l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_505 :
    hubcapFit theRedpart rf8 p8_492l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_505_1, c8_505_2, c8_505_3, c8_505_4, c8_505_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_489l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_507_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_489l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_507 :
    hubcapFit theRedpart rf8 p8_489l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_507_1, c8_507_2, c8_507_3, c8_507_4, c8_507_5, c8_507_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_509_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_509_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_509_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_488l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_509_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_488l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_509_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_488l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_509 :
    hubcapFit theRedpart rf8 p8_488l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_509_1, c8_509_2, c8_509_3, c8_509_4, c8_509_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_510_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_510_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_510_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_487l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_510_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_487l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_510_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_487l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_510 :
    hubcapFit theRedpart rf8 p8_487l
    (Hubcap.one 3 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_510_1, c8_510_2, c8_510_3, c8_510_4, c8_510_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_512_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_486l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_512_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_486l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_512_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_486l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_512_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_486l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_512 :
    hubcapFit theRedpart rf8 p8_486l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_512_1, c8_512_2, c8_512_3, c8_512_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_513_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_485l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_513_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_513_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_485l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_513_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_485l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_513_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_485l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_513 :
    hubcapFit theRedpart rf8 p8_485l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_513_1, c8_513_2, c8_513_3, c8_513_4, c8_513_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_484l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_484l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_515_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_484l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_515 :
    hubcapFit theRedpart rf8 p8_484l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_515_1, c8_515_2, c8_515_3, c8_515_4, c8_515_5, c8_515_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_483l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_483l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_483l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_483l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_483l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_516_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_483l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_516 :
    hubcapFit theRedpart rf8 p8_483l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_516_1, c8_516_2, c8_516_3, c8_516_4, c8_516_5, c8_516_6, c8_516_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_482l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_482l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_482l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_482l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_482l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_518_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_482l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_518 :
    hubcapFit theRedpart rf8 p8_482l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_518_1, c8_518_2, c8_518_3, c8_518_4, c8_518_5, c8_518_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_520_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_450l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_520_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_450l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_520_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_450l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_520_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_450l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_520_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_450l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_520 :
    hubcapFit theRedpart rf8 p8_450l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_520_1, c8_520_2, c8_520_3, c8_520_4, c8_520_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_521_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_449l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_521_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_449l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_521_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_449l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_521_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_449l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_521 :
    hubcapFit theRedpart rf8 p8_449l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_521_1, c8_521_2, c8_521_3, c8_521_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_523_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_523_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_523_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_448l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_523_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_448l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_523_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_448l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_523 :
    hubcapFit theRedpart rf8 p8_448l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_523_1, c8_523_2, c8_523_3, c8_523_4, c8_523_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_524_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_524_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_524_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_447l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_524_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_447l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_524_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_447l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_524 :
    hubcapFit theRedpart rf8 p8_447l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_524_1, c8_524_2, c8_524_3, c8_524_4, c8_524_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_535r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_535r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_535r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_535r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_535r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_536_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_535r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_536 :
    hubcapFit theRedpart rf8 p8_535r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_536_1, c8_536_2, c8_536_3, c8_536_4, c8_536_5, c8_536_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_537_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_535l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_537_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_535l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_537_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_535l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_537_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_535l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_537_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_535l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_537 :
    hubcapFit theRedpart rf8 p8_535l
    (Hubcap.one 1 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_537_1, c8_537_2, c8_537_3, c8_537_4, c8_537_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_534l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_534l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_534l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_534l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_534l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_539_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_534l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_539 :
    hubcapFit theRedpart rf8 p8_534l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_539_1, c8_539_2, c8_539_3, c8_539_4, c8_539_5, c8_539_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_540_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_540_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_540_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_533l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_540_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_533l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_540_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_533l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_540 :
    hubcapFit theRedpart rf8 p8_533l
    (Hubcap.one 1 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_540_1, c8_540_2, c8_540_3, c8_540_4, c8_540_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_532l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_532l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_542_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_532l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_542 :
    hubcapFit theRedpart rf8 p8_532l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_542_1, c8_542_2, c8_542_3, c8_542_4, c8_542_5, c8_542_6]

end FourColor

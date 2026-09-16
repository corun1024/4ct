import FourColor.Present8Step2
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 3 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1482 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1468 p8_1468l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1481
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1480 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1357 p8_1467r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1482 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 5 7 <|
       Hubcap.two 4 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1474
  intro _
  exact s8_step1473 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1486 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1357 p8_1465r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1485
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 4 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1484
  intro _
  exact s8_step1483 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1494 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1465 p8_1490r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1493
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1492

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1496 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1465 p8_1489r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1495
  intro _
  exact s8_step1494 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1498 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1465 p8_1488r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1497
  intro _
  exact s8_step1496 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1500 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1465 p8_1487r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1499
  intro _
  exact s8_step1498 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1502 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1465 p8_1465l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1501
  intro _
  exact s8_step1500 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1509 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1464 p8_1505r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1508
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1507

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1511 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1464 p8_1504r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1510
  intro _
  exact s8_step1509 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1513 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1464 p8_1503r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1512
  intro _
  exact s8_step1511 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1525 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1521r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1524
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1523

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1527 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1520r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1526
  intro _
  exact s8_step1525 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1529 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1519r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1528
  intro _
  exact s8_step1527 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1531 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1518r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1530
  intro _
  exact s8_step1529 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1534 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1516r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1533
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 6 7 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1532
  intro _
  exact s8_step1531 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1537 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1514r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1536
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1535
  intro _
  exact s8_step1534 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1539 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1463 p8_1463l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1538
  intro _
  exact s8_step1537 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1540 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1357 p8_1462r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1539 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1513 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1502 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1486 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1543 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1357 p8_1357l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1542
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1541
  intro _
  exact s8_step1540 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1545 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1177 p8_1355r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1544
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact s8_step1543 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s8_step1460 hred L1_1 L1_2 L2_1
  intro L4_1
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1450 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1547 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1177 p8_1354r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1546
  intro _
  exact s8_step1545 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1549 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1177 p8_1177l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1548
  intro _
  exact s8_step1547 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1550 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_733 p8_1176r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1549 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1353 hred L1_1 L1_2 L2_1
  intro L3_1
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1264 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1552 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_120 p8_732r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 6 5 <|
         Hubcap.two 0 1 4 <|
         Hubcap.two 3 4 4 <|
         Hubcap.two 5 7 7 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_1551
    intro _
    exact s8_step1550 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1175 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1597 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1593r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1596
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1595

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1600 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1591r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1599
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1598
  intro _
  exact s8_step1597 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1603 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1589r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1602
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1601
  intro _
  exact s8_step1600 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1612 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1588 p8_1608r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1611
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1610

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1614 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1588 p8_1606r := by
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1613
  intro _
  exact s8_step1612 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1616 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1588 p8_1605r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1615
  intro _
  exact s8_step1614 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1627 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1587r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact h8_1626 hred _
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1616 hred L1_1 L1_2 L3_1
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1603 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1659 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1585 p8_1655r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1658
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1657

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1662 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1585 p8_1653r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1661
  intro _
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1660
  intro _
  exact s8_step1659 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1670 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1585 p8_1651r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1669
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact h8_1668 hred _
  intro _
  exact s8_step1662 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1697 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1585 p8_1585l := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact h8_1696 hred _
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact h8_1686 hred _
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact h8_1676 hred _
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1670 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1699 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1583r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1698
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1697 hred L1_1 L1_2 L3_1
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact h8_1647 hred _
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact h8_1637 hred _
  intro _
  exact s8_step1627 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1711 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_1559 p8_1559l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact h8_1710 hred _
  intro _
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1700
  intro _
  exact s8_step1699 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1722 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L3_1 : Successful q8_1556) :
    SucceedsIn q8_731 p8_1557r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact h8_1721 hred _
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1711 hred L1_1 L1_2 L3_1
  intro L3_2
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact h8_1581 hred _
  intro _
  exact h8_1571 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1744 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1740r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1743
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1742

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1746 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1738r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1745
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1744 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1748 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1737r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1747
  intro _
  exact s8_step1746 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1750 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1736r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1749
  intro _
  exact s8_step1748 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1752 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1735r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1751
  intro _
  exact s8_step1750 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1754 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1734r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1753
  intro _
  exact s8_step1752 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1756 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1733r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1755
  intro _
  exact s8_step1754 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1758 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1732r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1757
  intro _
  exact s8_step1756 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1762 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1731 p8_1731l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1761
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1760

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1764 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1729r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1763
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1762 hred L1_1 L1_2
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1758 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1772 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1726r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1771
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact h8_1770 hred _
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1764 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1774 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1724r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1773
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1772 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1776 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1556 p8_1556l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 3 7 6 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1775
  intro _
  exact s8_step1774 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1813 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_731 p8_1553r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact h8_1812 hred _
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact h8_1794 hred _
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact s8_step1776 hred L1_1 L1_2
  intro L3_1
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1722 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1836 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1553 p8_1819r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact h8_1835 hred _
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1821

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1838 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1553 p8_1818r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1837
  intro _
  exact s8_step1836 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1854 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1553 p8_1816r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1853
  intro _
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact h8_1852 hred _
  intro _
  exact s8_step1838 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1874 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_1553 p8_1814r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.two 6 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1873
  intro _
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact h8_1872 hred _
  intro _
  exact s8_step1854 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1905 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118) :
    SucceedsIn q8_120 p8_120l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
      · exact h8_1904 hred _
      intro _
      exact s8_step1874 hred L1_1 L1_2
    intro _
    exact s8_step1813 hred L1_1 L1_2
  intro L2_1
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1552 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1931 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914)
    (L2_4 : Successful q8_1922) :
    SucceedsIn q8_118 p8_1927r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1930
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1929

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1933 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914)
    (L2_4 : Successful q8_1922) :
    SucceedsIn q8_118 p8_1925r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1932
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1931 hred L1_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1936 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914)
    (L2_4 : Successful q8_1922) :
    SucceedsIn q8_118 p8_1923r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1935
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1934
  intro _
  exact s8_step1933 hred L1_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1941 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914) :
    SucceedsIn q8_1922 p8_1937r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1940
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1939

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1943 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914) :
    SucceedsIn q8_118 p8_1920r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1942
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1941 hred L1_1 L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1936 hred L1_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1946 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914) :
    SucceedsIn q8_118 p8_1918r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1945
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1944
  intro _
  exact s8_step1943 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1948 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910)
    (L2_3 : Successful q8_1914) :
    SucceedsIn q8_118 p8_1917r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1947
  intro _
  exact s8_step1946 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1966 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1962r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1965
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1964

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1981 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1977r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1980
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1979

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1983 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1975r := by
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1982
  intro _
  exact s8_step1981 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1985 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1973r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1984
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1983 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1987 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1971r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1986
  intro _
  exact s8_step1985 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1989 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1969r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1988
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1987 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1991 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1968r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1990
  intro _
  exact s8_step1989 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1993 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1961 p8_1961l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1992
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1991 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1995 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1958r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1994
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1993 hred L1_1 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1966 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1998 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1956r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1997
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1996
  intro _
  exact s8_step1995 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2000 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1954r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1999
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1998 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2002 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1953r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2001
  intro _
  exact s8_step2000 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2005 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1951r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2004
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 4 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2003
  intro _
  exact s8_step2002 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2021 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2017r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2020
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2019

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2024 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2015r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2023
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2022
  intro _
  exact s8_step2021 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2026 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2013r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2025
  intro _
  exact s8_step2024 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2029 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2011r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2028
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2027
  intro _
  exact s8_step2026 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2031 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2009r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2030
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2029 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2033 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2008r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2032
  intro _
  exact s8_step2031 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2035 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2007r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2034
  intro _
  exact s8_step2033 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2037 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_2006r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2036
  intro _
  exact s8_step2035 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2039 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1950 p8_1950l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2038
  intro _
  exact s8_step2037 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2041 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_1914 p8_1914l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2040
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2039 hred L1_1 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2005 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2042 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_118 p8_1913r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2041 hred L1_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1948 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2044 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_118 p8_1912r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2043
  intro _
  exact s8_step2042 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2046 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L2_2 : Successful q8_1910) :
    SucceedsIn q8_118 p8_1911r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2045
  intro _
  exact s8_step2044 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2066 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2062r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2065
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2064

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2068 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2060r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2067
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2066 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2070 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2059r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2069
  intro _
  exact s8_step2068 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2075 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2058 p8_2071r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2074
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2073

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2077 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2057r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 4 2 <|
         Hubcap.one 7 3 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 2 3 5 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2076
    intro _
    exact s8_step2075 hred L1_1 L2_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2070 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2093 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2089r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2092
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2091

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2095 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2088r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2094
  intro _
  exact s8_step2093 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2097 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2086r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2096
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2095 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2104 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2085 p8_2100r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2103
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2102

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2106 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2085 p8_2099r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2105
  intro _
  exact s8_step2104 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2108 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2085 p8_2085l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2107
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2106 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2110 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2083r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2109
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2108 hred L1_1 L2_1
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2097 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2112 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2081r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2111
  intro _
  exact s8_step2110 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2115 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2079r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2114
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2113
  intro _
  exact s8_step2112 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2117 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2078r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2116
  intro _
  exact s8_step2115 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2119 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2056 p8_2056l := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2118
  intro _
  exact s8_step2117 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2121 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2054r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2120
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2119 hred L1_1 L2_1
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2077 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2138 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2134r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2137
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2136

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2140 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2133r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2139
  intro _
  exact s8_step2138 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2142 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2131r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2141
  intro _
  exact s8_step2140 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2144 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2129r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2143
  intro _
  exact s8_step2142 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2152 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2128 p8_2148r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2151
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2150

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2155 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2128 p8_2146r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2154
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2153
  intro _
  exact s8_step2152 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2157 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2128 p8_2128l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2156
  intro _
  exact s8_step2155 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2158 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2127r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2157 hred L1_1 L2_1
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2145
  intro _
  exact s8_step2144 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2161 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2125r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2160
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2159
  intro _
  exact s8_step2158 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2164 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2053 p8_2123r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2163
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2162
  intro _
  exact s8_step2161 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2123 p8_2123l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2167
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2166

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2169 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2052r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact s8_step2168 hred L1_1 L2_1
    intro _
    exact s8_step2164 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2122
  intro _
  exact s8_step2121 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2186 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2182r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2185
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2184

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2192 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2181 p8_2188r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2191
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2190

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2194 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2181 p8_2187r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2193
  intro _
  exact s8_step2192 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2196 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2181 p8_2181l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2195
  intro _
  exact s8_step2194 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2198 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2179r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2197
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2196 hred L1_1 L2_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2186 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2200 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2177r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2199
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2198 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2202 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2175r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2201
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2200 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2210 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2175 p8_2206r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2209
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2208

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2213 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2175 p8_2204r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2212
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2211
  intro _
  exact s8_step2210 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2215 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2175 p8_2203r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2214
  intro _
  exact s8_step2213 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2217 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2175 p8_2175l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2216
  intro _
  exact s8_step2215 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2219 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2173r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2218
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2217 hred L1_1 L2_1
  intro _
  exact s8_step2202 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2222 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2171r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2221
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2220
  intro _
  exact s8_step2219 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2224 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2051 p8_2051l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2223
  intro _
  exact s8_step2222 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2225 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2050r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2224 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2170
  intro _
  exact s8_step2169 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2248 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2244r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2247
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2246

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2250 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2242r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2249
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2248 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2252 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2241r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2251
  intro _
  exact s8_step2250 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2254 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2240r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 1 3 7 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2253
  intro _
  exact s8_step2252 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2256 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2239r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 1 3 7 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2255
  intro _
  exact s8_step2254 hred L1_1 L2_1 L4_1 L4_2

end FourColor

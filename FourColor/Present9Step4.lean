import FourColor.Present9Step3
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 4 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1620 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1554l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1619
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1618 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1622 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1552r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1621
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1620 hred L2_1 L3_1 L3_2 L3_3
  intro _
  exact s9_step1597 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1632 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1552 p9_1628r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1631
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1630

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1640 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1627 p9_1637r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1639

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1642 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1627 p9_1634r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1641
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1640 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1644 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1552 p9_1626r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap9 hred
        (Hubcap.one 4 4 <|
         Hubcap.one 7 4 <|
         Hubcap.one 8 4 <|
         Hubcap.two 0 1 4 <|
         Hubcap.two 2 3 7 <|
         Hubcap.two 5 6 7 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f9_1643
    intro _
    exact s9_step1642 hred L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1633
  intro _
  exact s9_step1632 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1646 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1552 p9_1625r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1645
  intro _
  exact s9_step1644 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1649 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1552 p9_1623r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1648
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1647
  intro _
  exact s9_step1646 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1651 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_1552 p9_1552l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1650
  intro _
  exact s9_step1649 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1653 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_794 p9_1550r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1652
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1651 hred L2_1 L3_1 L3_2
  intro L3_3
  exact s9_step1622 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1655 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547) :
    SucceedsIn q9_794 p9_1549r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1654
  intro _
  exact s9_step1653 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1681 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1677r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1680
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1679

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1683 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1675r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1682
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1681 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1685 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1672r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1684
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1683 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1687 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1670r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1686
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1685 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1689 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1668r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1688
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1687 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1691 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1667r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1690
  intro _
  exact s9_step1689 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1693 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1666r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1692
  intro _
  exact s9_step1691 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1695 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1665r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1694
  intro _
  exact s9_step1693 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1697 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1664r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1696
  intro _
  exact s9_step1695 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1699 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1661r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1698
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1697 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1701 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1660r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1700
  intro _
  exact s9_step1699 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1703 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1659r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1702
  intro _
  exact s9_step1701 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1718 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1714r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1717
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1716

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1720 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1713r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1719
  intro _
  exact s9_step1718 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1722 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1712r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1721
  intro _
  exact s9_step1720 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1725 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1710r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1724
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1723
  intro _
  exact s9_step1722 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1727 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1709r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1726
  intro _
  exact s9_step1725 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1730 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1707r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1729
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1728
  intro _
  exact s9_step1727 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1732 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1706r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1731
  intro _
  exact s9_step1730 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1734 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1705r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1733
  intro _
  exact s9_step1732 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1736 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1658 p9_1658l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1735
  intro _
  exact s9_step1734 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1737 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1657r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1736 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1704
  intro _
  exact s9_step1703 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1739 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1656r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1738
  intro _
  exact s9_step1737 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1741 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1547 p9_1547l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1740
  intro _
  exact s9_step1739 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1743 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1545r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1742
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1741 hred L2_1 L3_1
  intro L3_2
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1655 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1745 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1544r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1744
  intro _
  exact s9_step1743 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1747 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1543r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1746
  intro _
  exact s9_step1745 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1749 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1542r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1748
  intro _
  exact s9_step1747 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1751 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1541r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1750
  intro _
  exact s9_step1749 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1753 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_794 p9_1540r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1752
  intro _
  exact s9_step1751 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1768 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1764r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1767
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1766

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1770 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1763r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1769
  intro _
  exact s9_step1768 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1772 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1762r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1771
  intro _
  exact s9_step1770 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1774 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1761r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1773
  intro _
  exact s9_step1772 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1781 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1761 p9_1777r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1780
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1779

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1783 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1761 p9_1776r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1782
  intro _
  exact s9_step1781 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1785 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1761 p9_1775r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1784
  intro _
  exact s9_step1783 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1787 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1761 p9_1761l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1786
  intro _
  exact s9_step1785 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1804 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1800r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1803
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1802

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1806 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1798r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1805
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1804 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1808 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1796r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1807
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1806 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1810 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1795r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1809
  intro _
  exact s9_step1808 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1812 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1793r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1811
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1810 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1814 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1792r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1813
  intro _
  exact s9_step1812 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1816 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1791r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 5 7 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1815
  intro _
  exact s9_step1814 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1818 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1790r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 5 8 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1817
  intro _
  exact s9_step1816 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1823 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1788 p9_1819r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 8 8 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1822
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 3 7 8 <|
     Hubcap.two 3 8 8 <|
     Hubcap.two 4 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1821

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1825 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1760 p9_1760l := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap9 hred
        (Hubcap.one 2 3 <|
         Hubcap.one 3 5 <|
         Hubcap.one 8 4 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 4 7 7 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f9_1824
    intro _
    exact s9_step1823 hred L2_1 L3_1
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1818 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1846 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1757r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact h9_1845 hred _
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact h9_1835 hred _
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact s9_step1825 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s9_step1787 hred L2_1 L3_1
  intro _
  exact s9_step1774 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1873 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539) :
    SucceedsIn q9_1540 p9_1540l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact h9_1872 hred _
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact h9_1866 hred _
  intro _
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact h9_1860 hred _
  intro _
  exact s9_step1846 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1889 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1885r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1888
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1887

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1891 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1884r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1890
  intro _
  exact s9_step1889 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1898 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1883 p9_1894r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1897
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1896

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1900 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1883 p9_1893r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1899
  intro _
  exact s9_step1898 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1902 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1883 p9_1883l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1901
  intro _
  exact s9_step1900 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1903 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1882r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1902 hred L2_1 L4_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1892
  intro _
  exact s9_step1891 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1910 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1882 p9_1906r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.two 0 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1909
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1908

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1912 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1882 p9_1905r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1911
  intro _
  exact s9_step1910 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1914 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1882 p9_1904r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1913
  intro _
  exact s9_step1912 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1916 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1882 p9_1882l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1915
  intro _
  exact s9_step1914 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1918 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1880r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1917
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s9_step1916 hred L2_1 L4_1
  intro _
  exact s9_step1903 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1927 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1880 p9_1923r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1926
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1925

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1929 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1880 p9_1921r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1928
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1927 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1931 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1880 p9_1919r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1930
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1929 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1933 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1880 p9_1880l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1932
  intro _
  exact s9_step1931 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1945 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1877r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1944
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact h9_1943 hred _
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact s9_step1933 hred L2_1 L4_1
  intro _
  exact s9_step1918 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1947 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1876r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1946
  intro _
  exact s9_step1945 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1949 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_1874) :
    SucceedsIn q9_1539 p9_1875r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 4 6 8 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1948
  intro _
  exact s9_step1947 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1974 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1970r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1973
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1972

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1976 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1969r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1975
  intro _
  exact s9_step1974 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1978 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1967r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1977
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1976 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1980 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1966r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1979
  intro _
  exact s9_step1978 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1982 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1965r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1981
  intro _
  exact s9_step1980 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1984 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1963r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1983
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1982 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1986 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1961r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1985
  intro _
  exact s9_step1984 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1999 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1995r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1998
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1997

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2001 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1994r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2000
  intro _
  exact s9_step1999 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2003 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1993r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2002
  intro _
  exact s9_step2001 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2005 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1991r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2004
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2003 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2007 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1990r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2006
  intro _
  exact s9_step2005 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2009 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1989r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2008
  intro _
  exact s9_step2007 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2011 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1961 p9_1987r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2010
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2009 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2013 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1960r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap9 hred
        (Hubcap.one 1 4 <|
         Hubcap.one 4 3 <|
         Hubcap.one 8 4 <|
         Hubcap.two 0 7 6 <|
         Hubcap.two 2 3 5 <|
         Hubcap.two 5 6 8 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f9_2012
    intro _
    exact s9_step2011 hred L2_1 L5_1
  intro _
  exact s9_step1986 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2015 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1959r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2014
  intro _
  exact s9_step2013 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2017 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1957r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2016
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2015 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2027 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1954 p9_2023r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2026
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2025

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2038 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2020 p9_2034r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2037
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2036

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2040 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2020 p9_2032r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2039
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2038 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2042 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2020 p9_2028r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2041
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2040 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2044 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2020 p9_2020l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2043
  intro _
  exact s9_step2042 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2045 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1954 p9_2019r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2044 hred L2_1 L5_1
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2027 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2047 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1954 p9_2018r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2046
  intro _
  exact s9_step2045 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2049 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1954 p9_1954l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 8 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2048
  intro _
  exact s9_step2047 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2050 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1953r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2049 hred L2_1 L5_1
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2017 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2052 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1874 p9_1952r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 6 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2051
  intro _
  exact s9_step2050 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2071 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1952 p9_2058r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact h9_2070 hred _
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2060

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2082 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_1952 p9_2054r := by
  refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact h9_2081 hred _
  intro _
  exact s9_step2071 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2098 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2095r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2097

end FourColor

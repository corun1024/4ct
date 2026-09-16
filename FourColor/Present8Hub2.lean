import FourColor.Present8Hub1

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 2 of the arity 8 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1692 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1688r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1691

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1693 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1687l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1690 hred _
  intro _
  exact h8_1692 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1695 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1687r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1694

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1696 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1648l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1693 hred _
  intro _
  exact h8_1695 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1704 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1702l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1703

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1706 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1702r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1705

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1707 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1701l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1704 hred _
  intro _
  exact h8_1706 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1709 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1701r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1708

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1710 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1582l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1707 hred _
  intro _
  exact h8_1709 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1715 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1713l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1714

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1717 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1713r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1716

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1718 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1712l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1715 hred _
  intro _
  exact h8_1717 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1720 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1712r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1719

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1721 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1558l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1718 hred _
  intro _
  exact h8_1720 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1767 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1765l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1766

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1769 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1765r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1768

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1770 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1728l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h8_1767 hred _
  intro _
  exact h8_1769 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1779 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1777l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1778

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1782 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1780l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1781

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1786 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1784l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1785

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1788 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1784r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1787

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1789 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1783l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1786 hred _
  intro _
  exact h8_1788 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1791 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1783r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1790

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1792 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1780r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1789 hred _
  intro _
  exact h8_1791 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1793 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1777r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h8_1782 hred _
  intro _
  exact h8_1792 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1794 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1555l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h8_1779 hred _
  intro _
  exact h8_1793 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1797 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1795l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1796

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1800 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1798l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1799

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1804 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1802l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1803

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1806 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1802r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1805

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1807 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1801l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1804 hred _
  intro _
  exact h8_1806 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1809 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1801r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1808

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1810 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1798r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1807 hred _
  intro _
  exact h8_1809 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1811 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1795r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h8_1800 hred _
  intro _
  exact h8_1810 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1812 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1554l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h8_1797 hred _
  intro _
  exact h8_1811 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1825 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1823l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1824

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1827 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1823r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1826

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1828 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1822l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h8_1825 hred _
  intro _
  exact h8_1827 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1831 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1829l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1830

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1833 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1829r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1832

end FourColor

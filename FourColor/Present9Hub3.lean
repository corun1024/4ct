import FourColor.Present9Hub2

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 3 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1521 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1519l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1520

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1524 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1522l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1523

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1528 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1526l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1527

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1530 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1526r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1529

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1531 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1525l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact h9_1528 hred _
  intro _
  exact h9_1530 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1533 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1525r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1532

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1534 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1522r := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_1531 hred _
  intro _
  exact h9_1533 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1535 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1519r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_1524 hred _
  intro _
  exact h9_1534 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1536 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_916l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_1521 hred _
  intro _
  exact h9_1535 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1828 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1826l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1827

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1831 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1829l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1830

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1833 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1829r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1832

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1834 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1826r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_1831 hred _
  intro _
  exact h9_1833 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1835 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1759l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_1828 hred _
  intro _
  exact h9_1834 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1838 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1836l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1837

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1841 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1839l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1840

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1843 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1839r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1842

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1844 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1836r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_1841 hred _
  intro _
  exact h9_1843 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1845 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1758l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_1838 hred _
  intro _
  exact h9_1844 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1850 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1848l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1849

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1852 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1848r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1851

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1853 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1847l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_1850 hred _
  intro _
  exact h9_1852 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1856 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1854l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1855

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1858 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1854r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1857

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1859 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1847r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_1856 hred _
  intro _
  exact h9_1858 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1860 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1757l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h9_1853 hred _
  intro _
  exact h9_1859 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1863 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1861l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1862

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1865 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1861r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1864

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1866 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1756l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_1863 hred _
  intro _
  exact h9_1865 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1869 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1867l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1868

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1871 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1867r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1870

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1872 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1755l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_1869 hred _
  intro _
  exact h9_1871 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1936 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1934l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1935

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1939 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1937l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1938

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1941 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1937r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1940

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1942 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1934r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_1939 hred _
  intro _
  exact h9_1941 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_1943 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1879l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_1936 hred _
  intro _
  exact h9_1942 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2063 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2061l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2062

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2066 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2064l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2065

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2068 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2064r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2067

end FourColor

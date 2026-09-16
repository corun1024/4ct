import FourColor.Present8Hub2

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 3 of the arity 8 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1834 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1822r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h8_1831 hred _
  intro _
  exact h8_1833 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1835 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1820l := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact h8_1828 hred _
  intro _
  exact h8_1834 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1841 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1839l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1840

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1845 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1843l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1844

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1847 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1843r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1846

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1848 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1842l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1845 hred _
  intro _
  exact h8_1847 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1850 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1842r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1849

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1851 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1839r := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h8_1848 hred _
  intro _
  exact h8_1850 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1852 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1818l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h8_1841 hred _
  intro _
  exact h8_1851 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1857 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1855l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1856

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1860 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1858l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1859

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1864 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1862l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1863

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1866 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1862r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1865

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1867 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1861l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h8_1864 hred _
  intro _
  exact h8_1866 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1869 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1861r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1868

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1870 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1858r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1867 hred _
  intro _
  exact h8_1869 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1871 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1855r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h8_1860 hred _
  intro _
  exact h8_1870 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1872 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1816l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h8_1857 hred _
  intro _
  exact h8_1871 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1880 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1878l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1879

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1882 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1878r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1881

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1883 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1877l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h8_1880 hred _
  intro _
  exact h8_1882 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1886 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1884l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1885

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1888 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1884r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1887

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1889 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1877r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h8_1886 hred _
  intro _
  exact h8_1888 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1890 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1876l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h8_1883 hred _
  intro _
  exact h8_1889 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1893 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1891l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1892

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1895 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1891r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1894

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1896 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1876r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h8_1893 hred _
  intro _
  exact h8_1895 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1897 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1875l := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h8_1890 hred _
  intro _
  exact h8_1896 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1900 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1898l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1899

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1902 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1898r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 2 6 9 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1901

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1903 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1875r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h8_1900 hred _
  intro _
  exact h8_1902 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_1904 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_1814l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact h8_1897 hred _
  intro _
  exact h8_1903 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2572 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2570l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2571

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2574 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2570r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2573

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2575 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2564l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h8_2572 hred _
  intro _
  exact h8_2574 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2578 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2576l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2577

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2580 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2576r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2579

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2581 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2563l := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact h8_2578 hred _
  intro _
  exact h8_2580 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2595 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2593l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2594

end FourColor

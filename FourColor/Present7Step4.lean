import FourColor.Present7Step3
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 4 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1885 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1831 p7_1877r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1884
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1883 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1886 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_883 p7_1830r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_6
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step1885 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step1875 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1860 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1891 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825)
    (L2_6 : Successful q7_1828) :
    SucceedsIn q7_1829 p7_1887r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1890
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1889

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1901 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1828 p7_1898r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1900

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1903 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1828 p7_1896r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1902
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1901 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1905 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1828 p7_1893r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1904
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1903 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1906 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_883 p7_1827r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step1905 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro L2_6
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_5
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step1891 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1886 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1923 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1919r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1922

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1925 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1918r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1924
  intro _
  exact s7_step1923 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1927 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1916r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1926
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1925 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1935 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1913 p7_1930r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1934
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1933

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1937 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1913 p7_1928r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1936
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1935 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1938 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1912r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step1937 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1927 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1952 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1948r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1951
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1950

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1955 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1946r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1954
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1953
  intro _
  exact s7_step1952 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1957 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1945r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1956
  intro _
  exact s7_step1955 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1959 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1944r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1958
  intro _
  exact s7_step1957 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1961 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1942r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1960
  intro _
  exact s7_step1959 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1963 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1940r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1962
  intro _
  exact s7_step1961 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1969 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1940 p7_1965r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1968
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1967

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1971 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1940 p7_1940l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1970
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1969 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1977 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1939 p7_1973r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1976
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1975

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1983 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1972 p7_1979r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1982
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1981

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1985 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1972 p7_1972l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1984
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1983 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1986 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1912 p7_1912l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step1985 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
    intro _
    refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step1977 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1971 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step1963 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1993 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1911 p7_1989r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1992
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1991

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2000 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1989 p7_1996r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1999
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1998

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2002 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1989 p7_1994r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2001
  intro _
  exact s7_step2000 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2004 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1911 p7_1988r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 3 2 <|
         Hubcap.one 6 2 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 4 5 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2003
    intro _
    exact s7_step2002 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step1993 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2007 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1911 p7_1911l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2006
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 6 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2005
  intro _
  exact s7_step2004 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2019 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1910 p7_2015r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2018
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2017

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2022 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1910 p7_2013r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2021
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2020
  intro _
  exact s7_step2019 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2024 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1910 p7_2010r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2023
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2022 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2026 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1910 p7_2009r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2025
  intro _
  exact s7_step2024 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2027 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1909r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2026 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2007 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1986 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step1938 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2033 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1909 p7_2029r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2032
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2031

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2035 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1909 p7_1909l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2034
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2033 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2051 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2047r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2050

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2053 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2046r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2052
  intro _
  exact s7_step2051 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2055 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2043r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2054
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2053 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2061 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2040 p7_2057r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 5 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2060
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2059

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2063 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2040 p7_2040l := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2062
  intro _
  exact s7_step2061 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2064 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2039r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2063 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2055 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2073 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2039 p7_2069r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2072
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2071

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2075 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2039 p7_2066r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2074
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2073 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2080 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2066 p7_2076r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2079
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2078

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2082 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2039 p7_2065r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 1 <|
         Hubcap.two 0 2 3 <|
         Hubcap.two 3 6 4 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2081
    intro _
    exact s7_step2080 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step2075 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2084 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2038r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 1 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 0 2 3 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2083
    intro _
    exact s7_step2082 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step2064 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2089 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2038 p7_2085r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2088
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2087

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2091 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1908 p7_2037r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 1 <|
         Hubcap.one 5 1 <|
         Hubcap.one 6 2 <|
         Hubcap.two 0 2 3 <|
         Hubcap.two 3 4 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2090
    intro _
    exact s7_step2089 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step2084 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2097 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2037 p7_2093r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2096
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2095

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2100 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_2037 p7_2037l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2099
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2098
  intro _
  exact s7_step2097 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

end FourColor

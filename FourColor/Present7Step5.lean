import FourColor.Present7Step4
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 5 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2101 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824)
    (L2_5 : Successful q7_1825) :
    SucceedsIn q7_1826 p7_1907r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact s7_step2100 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
    intro _
    exact s7_step2091 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step2035 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step2027 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2114 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_1825 p7_2110r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2113
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2112

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2122 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2109 p7_2118r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2121
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2120

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2125 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2109 p7_2116r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2124
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2123
  intro _
  exact s7_step2122 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2127 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2109 p7_2115r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2126
  intro _
  exact s7_step2125 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2129 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_1825 p7_2108r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 4 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2128
    intro _
    exact s7_step2127 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2114 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2131 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_1825 p7_2107r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2130
  intro _
  exact s7_step2129 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2138 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2106 p7_2134r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2137
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2136

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2140 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2106 p7_2132r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2139
  intro _
  exact s7_step2138 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2142 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_1825 p7_2105r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 3 4 3 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2141
    intro _
    exact s7_step2140 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2131 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2150 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2105 p7_2146r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2149
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2148

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2154 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2144 p7_2144l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2153
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2152

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2156 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2105 p7_2105l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2155
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2154 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2150 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2166 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2103 p7_2162r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2165
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2164

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2103 p7_2160r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2167
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2166 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2179 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2160 p7_2175r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2178
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2181 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2160 p7_2174r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2180
  intro _
  exact s7_step2179 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2183 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2160 p7_2172r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2182
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2181 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2185 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2160 p7_2169r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2184
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2183 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2187 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2103 p7_2159r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 2 0 <|
         Hubcap.one 6 3 <|
         Hubcap.two 1 5 2 <|
         Hubcap.two 3 4 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2186
    intro _
    exact s7_step2185 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step2168 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2195 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2158 p7_2191r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2194
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2198 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2158 p7_2189r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2197
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2196
  intro _
  exact s7_step2195 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2201 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2158 p7_2158l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2200
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2199
  intro _
  exact s7_step2198 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2210 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2157 p7_2206r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2209
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2208

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2212 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2157 p7_2205r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2211
  intro _
  exact s7_step2210 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2214 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2157 p7_2203r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2213
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2212 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2216 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2157 p7_2157l := by
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2215
  intro _
  exact s7_step2214 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2217 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_1825 p7_2102r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact s7_step2216 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2201 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
    intro _
    refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2187 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s7_step2156 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step2142 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2227 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2102 p7_2223r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2226
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2225

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2229 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2102 p7_2220r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2228
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2227 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2235 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2220 p7_2232r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2234

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2238 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2220 p7_2230r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2237
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2236
  intro _
  exact s7_step2235 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2240 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2102 p7_2219r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 1 3 3 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2239
    intro _
    exact s7_step2238 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step2229 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2255 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2251r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2254
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2253

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2257 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2250r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2256
  intro _
  exact s7_step2255 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2260 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2248r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2259
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2258
  intro _
  exact s7_step2257 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2262 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2246r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 1 5 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2261
  intro _
  exact s7_step2260 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2265 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2244r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2264
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2263
  intro _
  exact s7_step2262 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2267 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2243r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2266
  intro _
  exact s7_step2265 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2270 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2218 p7_2241r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2269
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2268
  intro _
  exact s7_step2267 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2272 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_2102 p7_2102l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 2 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2271
    intro _
    exact s7_step2270 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2240 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2273 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L2_4 : Successful q7_1824) :
    SucceedsIn q7_883 p7_1824r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2272 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
    intro _
    exact s7_step2217 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4
  intro L2_5
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_4
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step2101 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1906 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2289 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276)
    (L3_2 : Successful q7_2278) :
    SucceedsIn q7_1824 p7_2285r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2288
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2287

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2291 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276)
    (L3_2 : Successful q7_2278) :
    SucceedsIn q7_1824 p7_2283r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2290
  intro _
  exact s7_step2289 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2293 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276)
    (L3_2 : Successful q7_2278) :
    SucceedsIn q7_1824 p7_2281r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2292
  intro _
  exact s7_step2291 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2302 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2278 p7_2298r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2301

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2305 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2278 p7_2296r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2304
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2303
  intro _
  exact s7_step2302 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2311 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2296 p7_2307r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2310
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2309

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2296 p7_2296l := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.two 0 3 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2313
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2312
  intro _
  exact s7_step2311 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2316 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2278 p7_2294r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2315
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact s7_step2314 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step2305 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2317 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_1824 p7_2277r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2316 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro L3_2
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2293 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2330 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2326r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2329
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2328

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2333 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2324r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2332
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2331
  intro _
  exact s7_step2330 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2335 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2321r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2334
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2333 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2337 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2319r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2336
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2335 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2342 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2319 p7_2338r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2341
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2340

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2344 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2318r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 2 1 <|
         Hubcap.one 3 0 <|
         Hubcap.two 1 5 3 <|
         Hubcap.two 4 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2343
    intro _
    exact s7_step2342 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step2337 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2359 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2318 p7_2355r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2358
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2357

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2361 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2318 p7_2353r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2360
  intro _
  exact s7_step2359 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2364 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2318 p7_2351r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2363
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 1 <|
       Hubcap.two 2 6 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2362
  intro _
  exact s7_step2361 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2368 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2351 p7_2351l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2367
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2366

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2377 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2350 p7_2373r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2376
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2375

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2379 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2350 p7_2371r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2378
  intro _
  exact s7_step2377 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2381 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2350 p7_2369r := by
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2380
  intro _
  exact s7_step2379 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2383 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2318 p7_2348r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2382
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2381 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact s7_step2368 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step2364 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2386 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2318 p7_2346r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2385
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2384
  intro _
  exact s7_step2383 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2394 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2345 p7_2390r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2393
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2392

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2396 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2345 p7_2387r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2395
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2394 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2397 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L3_1 : Successful q7_2276) :
    SucceedsIn q7_2277 p7_2277l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 6 true L3_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s7_step2396 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
    intro _
    refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2386 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step2344 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2412 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2408r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2411
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2410

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2415 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2406r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2414
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2413
  intro _
  exact s7_step2412 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2417 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2404r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2416
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2415 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2420 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2402r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2419
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 1 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2418
  intro _
  exact s7_step2417 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2429 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2402 p7_2425r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2428
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2427

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2432 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2402 p7_2423r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2431
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2430
  intro _
  exact s7_step2429 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2435 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2402 p7_2421r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2434
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2433
  intro _
  exact s7_step2432 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2437 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2401r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.two 4 6 3 <|
         Hubcap.two 2 3 4 <|
         Hubcap.two 2 5 3 <|
         Hubcap.two 3 5 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2436
    intro _
    exact s7_step2435 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  exact s7_step2420 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2444 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2401 p7_2440r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2443
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2442

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2446 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2401 p7_2438r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2445
  intro _
  exact s7_step2444 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2451 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2438 p7_2447r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2450
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2449

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2453 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2401 p7_2401l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 4 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2452
    intro _
    exact s7_step2451 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  exact s7_step2446 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2461 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2400 p7_2457r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2460
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2459

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2463 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2400 p7_2455r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2462
  intro _
  exact s7_step2461 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2469 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2455 p7_2464r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2468
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2467

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2471 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2400 p7_2454r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 1 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2470
    intro _
    exact s7_step2469 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  exact s7_step2463 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2478 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2399 p7_2473r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 6 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2477
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2476

end FourColor

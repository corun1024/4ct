import FourColor.Present9Step4
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 5 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2099 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2091r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2098 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2101 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2089r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2100
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2099 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2103 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2088r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2102
  intro _
  exact s9_step2101 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2105 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2087r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2104
  intro _
  exact s9_step2103 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2107 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2054 p9_2086r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2106
  intro _
  exact s9_step2105 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2114 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2086 p9_2111r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2113

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2116 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951)
    (L7_1 : Successful q9_2085) :
    SucceedsIn q9_2086 p9_2086l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 8 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2115
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L7_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2114 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2124 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2085 p9_2120r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2123
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2122

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2126 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2085 p9_2117r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2125
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2124 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2128 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2054 p9_2083r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 4 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2127
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step2126 hred L2_1 L5_1
  intro L7_1
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact s9_step2116 hred L2_1 L5_1 L7_1
  intro _
  exact s9_step2107 hred L2_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2130 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_1951) :
    SucceedsIn q9_2054 p9_2054l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2129
  intro _
  exact s9_step2128 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2178 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2174r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2177
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2180 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2173r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2179
  intro _
  exact s9_step2178 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2182 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2172r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 6 <|
       Hubcap.two 3 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2181
  intro _
  exact s9_step2180 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2184 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2171r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2183
  intro _
  exact s9_step2182 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2186 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2170r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2185
  intro _
  exact s9_step2184 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2188 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2169r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2187
  intro _
  exact s9_step2186 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2190 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2167r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2189
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2188 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2192 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2166r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2191
  intro _
  exact s9_step2190 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2194 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2165r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2193
  intro _
  exact s9_step2192 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2202 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2163r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2201
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h9_2200 hred _
  intro _
  exact s9_step2194 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2204 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2162r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 3 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2203
  intro _
  exact s9_step2202 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2212 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2160r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 6 8 <|
       Hubcap.two 3 8 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2211
  intro _
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact h9_2210 hred _
  intro _
  exact s9_step2204 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2214 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_2159r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 4 7 <|
       Hubcap.two 3 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2213
  intro _
  exact s9_step2212 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2230 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2226r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2229
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2228

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2232 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2224r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2231
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2230 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2234 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2222r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2233
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2232 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2236 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2221r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
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
      rfl (by decide +kernel) (by decide +kernel) f9_2235
  intro _
  exact s9_step2234 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2238 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2220r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2237
  intro _
  exact s9_step2236 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2243 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2219 p9_2239r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2242
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2241

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2245 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2219 p9_2219l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2244
  intro _
  exact s9_step2243 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2247 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2217r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2246
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2245 hred L2_1
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2238 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2249 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2216r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2248
  intro _
  exact s9_step2247 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2251 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2215r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2250
  intro _
  exact s9_step2249 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2253 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2159 p9_2159l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 5 7 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2252
  intro _
  exact s9_step2251 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2275 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2271r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2274
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2273

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2277 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2269r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2276
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2275 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2279 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2268r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2278
  intro _
  exact s9_step2277 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2281 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2265r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2280
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2279 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2283 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2263r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2282
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2281 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2285 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2157 p9_2260r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2284
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2283 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2286 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1951 p9_1951l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step2285 hred L2_1
  intro _
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact h9_2259 hred _
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2253 hred L2_1
  intro _
  exact s9_step2214 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2287 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1874 p9_1950r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2286 hred L2_1
  intro L5_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact h9_2156 hred _
    intro _
    refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
    · exact s9_step2130 hred L2_1 L5_1
    intro _
    exact s9_step2082 hred L2_1 L5_1
  intro _
  exact s9_step2052 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2310 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_794 p9_1538r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
      · exact h9_2309 hred _
      intro _
      exact s9_step2287 hred L2_1
    intro L4_1
    refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step1949 hred L2_1 L4_1
  intro L3_1
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact s9_step1873 hred L2_1 L3_1
  intro _
  exact s9_step1753 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2339 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2335r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2338
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2337

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2341 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2334r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2340
  intro _
  exact s9_step2339 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2343 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2333r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2342
  intro _
  exact s9_step2341 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2345 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2331r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2344
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2343 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2347 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2329r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2346
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2345 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2349 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2328r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2348
  intro _
  exact s9_step2347 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2351 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2327r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2350
  intro _
  exact s9_step2349 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2355 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_2327 p9_2327l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2354
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2353

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2357 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2325r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2356
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2355 hred L2_1 L4_1 L4_2
  intro _
  exact s9_step2351 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2359 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319)
    (L4_2 : Successful q9_2321) :
    SucceedsIn q9_1538 p9_2324r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2358
  intro _
  exact s9_step2357 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2367 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_2321 p9_2363r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2366
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 3 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2365

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2369 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_2321 p9_2362r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2368
  intro _
  exact s9_step2367 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2371 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_2321 p9_2361r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2370
  intro _
  exact s9_step2369 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2373 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_2321 p9_2360r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2372
  intro _
  exact s9_step2371 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2375 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_2321 p9_2321l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2374
  intro _
  exact s9_step2373 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2376 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L4_1 : Successful q9_2319) :
    SucceedsIn q9_1538 p9_2320r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2375 hred L2_1 L4_1
  intro L4_2
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2359 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2385 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2319 p9_2382r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2384

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2396 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2392r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2395
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2394

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2398 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2391r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2397
  intro _
  exact s9_step2396 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2400 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2389r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2399
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2398 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2402 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2388r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2401
  intro _
  exact s9_step2400 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2404 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2387r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2403
  intro _
  exact s9_step2402 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2406 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2381 p9_2381l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2405
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2404 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2408 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2378) :
    SucceedsIn q9_2319 p9_2379r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2407
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2406 hred L2_1 L5_1
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2385 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2418 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2378 p9_2414r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 8 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2417
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2416

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2420 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2378 p9_2413r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2419
  intro _
  exact s9_step2418 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2422 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2378 p9_2412r := by
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
      rfl (by decide +kernel) (by decide +kernel) f9_2421
  intro _
  exact s9_step2420 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2424 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2378 p9_2410r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2423
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2422 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2426 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2378 p9_2378l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2425
  intro _
  exact s9_step2424 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2427 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2319 p9_2377r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2426 hred L2_1
  intro L5_1
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2409
  intro _
  exact s9_step2408 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2429 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_2317r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2428
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step2427 hred L2_1
  intro L4_1
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2376 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2431 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_2316r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2430
  intro _
  exact s9_step2429 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2433 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_2315r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2432
  intro _
  exact s9_step2431 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2435 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_2314r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2434
  intro _
  exact s9_step2433 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2437 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_2313r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2436
  intro _
  exact s9_step2435 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2447 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440)
    (L5_2 : Successful q9_2444) :
    SucceedsIn q9_2313 p9_2444r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2446

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2455 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2444 p9_2451r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2454
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2453

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2457 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2444 p9_2450r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2456
  intro _
  exact s9_step2455 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2459 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2444 p9_2449r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2458
  intro _
  exact s9_step2457 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2461 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2444 p9_2448r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2460
  intro _
  exact s9_step2459 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2463 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2444 p9_2444l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2462
  intro _
  exact s9_step2461 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2465 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2313 p9_2442r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2464
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2463 hred L2_1 L5_1
  intro L5_2
  exact s9_step2447 hred L2_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2467 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L5_1 : Successful q9_2440) :
    SucceedsIn q9_2313 p9_2441r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2466
  intro _
  exact s9_step2465 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2478 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2440 p9_2474r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2477
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2476

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2481 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2440 p9_2472r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2480
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2479
  intro _
  exact s9_step2478 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2483 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2440 p9_2471r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2482
  intro _
  exact s9_step2481 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2494 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2490r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2493
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2492

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2496 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2489r := by
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2495
  intro _
  exact s9_step2494 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2499 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2487r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2498
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2497
  intro _
  exact s9_step2496 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2501 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2486r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2500
  intro _
  exact s9_step2499 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2503 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2485r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2502
  intro _
  exact s9_step2501 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2505 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2484r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2504
  intro _
  exact s9_step2503 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2507 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2470 p9_2470l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2506
  intro _
  exact s9_step2505 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2509 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2440 p9_2468r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2508
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2507 hred L2_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2483 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2524 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_2313 p9_2438r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact h9_2523 hred _
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step2509 hred L2_1
  intro L5_1
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2467 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2539 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_1538 p9_1538l := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact h9_2538 hred _
    intro _
    exact s9_step2524 hred L2_1
  intro _
  exact s9_step2437 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2540 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792) :
    SucceedsIn q9_14 p9_792r := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact s9_step2539 hred L2_1
    intro _
    exact s9_step2310 hred L2_1
  intro L2_2
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step1537 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2578 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2574r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2577
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2576

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2580 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2572r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2579
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2578 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2582 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2570r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2581
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2580 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2584 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2567r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2583
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2582 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2586 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2566r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2585
  intro _
  exact s9_step2584 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2588 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2564r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2587
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2586 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2590 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2562r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2589
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2588 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2592 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2560r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 7 8 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2591
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2590 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2594 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2559r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2593
  intro _
  exact s9_step2592 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2596 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_2557 p9_2557l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2595
  intro _
  exact s9_step2594 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2598 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2555r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2597
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2596 hred L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2600 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2554r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2599
  intro _
  exact s9_step2598 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2602 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2553r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2601
  intro _
  exact s9_step2600 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2604 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2552r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2603
  intro _
  exact s9_step2602 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2607 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2550r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2606
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2605
  intro _
  exact s9_step2604 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2609 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2549r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2608
  intro _
  exact s9_step2607 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2611 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2548r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2610
  intro _
  exact s9_step2609 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2614 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L3_3 : Successful q9_2545) :
    SucceedsIn q9_792 p9_2546r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2613
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2612
  intro _
  exact s9_step2611 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2637 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2633r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2636
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2635

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2639 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2632r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2638
  intro _
  exact s9_step2637 hred L3_1 L3_2

end FourColor

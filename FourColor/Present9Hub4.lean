import FourColor.Present9Hub3

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 4 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2069 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2061r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h9_2066 hred _
  intro _
  exact h9_2068 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2070 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2059l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_2063 hred _
  intro _
  exact h9_2069 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2074 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2072l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2073

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2077 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2075l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2076

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2079 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2075r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2078

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2080 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2072r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h9_2077 hred _
  intro _
  exact h9_2079 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2081 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2058l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_2074 hred _
  intro _
  exact h9_2080 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2134 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2132l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2133

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2139 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2137l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2138

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2141 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2137r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2140

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2142 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2136l := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact h9_2139 hred _
  intro _
  exact h9_2141 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2145 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2143l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2144

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2147 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2143r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2146

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2148 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2136r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h9_2145 hred _
  intro _
  exact h9_2147 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2149 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2135l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_2142 hred _
  intro _
  exact h9_2148 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2151 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2135r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2150

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2152 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2132r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_2149 hred _
  intro _
  exact h9_2151 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2153 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2131l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_2134 hred _
  intro _
  exact h9_2152 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2155 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2131r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2154

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2156 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2053l := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_2153 hred _
  intro _
  exact h9_2155 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2197 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2195l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2196

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2199 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2195r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2198

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2200 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2165l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h9_2197 hred _
  intro _
  exact h9_2199 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2207 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2205l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2206

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2209 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2205r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2208

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2210 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2162l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_2207 hred _
  intro _
  exact h9_2209 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2256 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2254l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2255

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2258 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2254r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2257

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2259 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2158l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_2256 hred _
  intro _
  exact h9_2258 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2293 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2291l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2292

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2295 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2291r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2294

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2296 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2290l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact h9_2293 hred _
  intro _
  exact h9_2295 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2299 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2297l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2298

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2301 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2297r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2300

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2302 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2290r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h9_2299 hred _
  intro _
  exact h9_2301 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2303 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2289l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_2296 hred _
  intro _
  exact h9_2302 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2305 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2289r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2304

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2306 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2288l := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact h9_2303 hred _
  intro _
  exact h9_2305 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2308 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2288r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2307

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2309 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_1950l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_2306 hred _
  intro _
  exact h9_2308 hred _

end FourColor

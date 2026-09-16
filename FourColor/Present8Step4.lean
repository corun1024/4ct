import FourColor.Present8Step3
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 4 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2258 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2237r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2257
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2256 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2260 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2236r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2259
  intro _
  exact s8_step2258 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2263 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229)
    (L4_2 : Successful q8_2231) :
    SucceedsIn q8_2050 p8_2234r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2262
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2261
  intro _
  exact s8_step2260 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2270 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229) :
    SucceedsIn q8_2231 p8_2266r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2269
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2268

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2272 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229) :
    SucceedsIn q8_2231 p8_2265r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2271
  intro _
  exact s8_step2270 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2275 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229) :
    SucceedsIn q8_2231 p8_2231l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2274
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2273
  intro _
  exact s8_step2272 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2276 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L4_1 : Successful q8_2229) :
    SucceedsIn q8_2050 p8_2230r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2275 hred L1_1 L2_1 L4_1
  intro L4_2
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2263 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2289 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2285r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2288
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2287

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2291 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2284r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2290
  intro _
  exact s8_step2289 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2293 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2283r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2292
  intro _
  exact s8_step2291 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2296 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2281r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2295
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2294
  intro _
  exact s8_step2293 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2298 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2280r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2297
  intro _
  exact s8_step2296 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2300 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2279r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2299
  intro _
  exact s8_step2298 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2302 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2278r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2301
  intro _
  exact s8_step2300 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2304 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2277r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2303
  intro _
  exact s8_step2302 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2306 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2229 p8_2229l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2305
  intro _
  exact s8_step2304 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908)
    (L5_1 : Successful q8_2310) :
    SucceedsIn q8_2228 p8_2310r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2313

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2319 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2310 p8_2315r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2318
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2317

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2321 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2310 p8_2310l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2320
  intro _
  exact s8_step2319 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2323 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2228 p8_2308r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2322
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2321 hred L1_1 L2_1
  intro L5_1
  exact s8_step2314 hred L1_1 L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2325 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2228 p8_2307r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2324
  intro _
  exact s8_step2323 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2327 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2228 p8_2228l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2326
  intro _
  exact s8_step2325 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2050 p8_2226r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2328
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2327 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2306 hred L1_1 L2_1
  intro L4_1
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2276 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2331 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_2050 p8_2050l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2330
  intro _
  exact s8_step2329 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2333 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_2048r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2332
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2331 hred L1_1 L2_1
  intro _
  exact s8_step2225 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2336 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L2_1 : Successful q8_1908) :
    SucceedsIn q8_1910 p8_1910l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2335
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2334
  intro _
  exact s8_step2333 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2355 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344)
    (L3_4 : Successful q8_2347) :
    SucceedsIn q8_1908 p8_2351r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2354
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2353

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2357 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344)
    (L3_4 : Successful q8_2347) :
    SucceedsIn q8_1908 p8_2350r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2356
  intro _
  exact s8_step2355 hred L1_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2359 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344)
    (L3_4 : Successful q8_2347) :
    SucceedsIn q8_1908 p8_2349r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2358
  intro _
  exact s8_step2357 hred L1_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2361 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344)
    (L3_4 : Successful q8_2347) :
    SucceedsIn q8_1908 p8_2348r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2360
  intro _
  exact s8_step2359 hred L1_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2371 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2347 p8_2367r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2370
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2369

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2373 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2347 p8_2364r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2372
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2371 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2376 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2347 p8_2362r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2375
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2374
  intro _
  exact s8_step2373 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2391 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2387r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2390
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2389

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2393 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2385r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2392
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2391 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2395 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2382r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2394
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2393 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2397 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2380r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2396
  intro _
  exact s8_step2395 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2400 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2378r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2399
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2398
  intro _
  exact s8_step2397 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2403 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_2346 p8_2346l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2402
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2401
  intro _
  exact s8_step2400 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2404 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342)
    (L3_3 : Successful q8_2344) :
    SucceedsIn q8_1908 p8_2345r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2403 hred L1_1 L3_1 L3_2 L3_3
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2376 hred L1_1 L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2361 hred L1_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2417 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2413r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2416
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2415

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2419 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2412r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2418
  intro _
  exact s8_step2417 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2421 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2410r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2420
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2419 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2423 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2408r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2422
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2421 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2425 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2407r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2424
  intro _
  exact s8_step2423 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2434 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2407 p8_2430r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2433
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2432

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2436 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2407 p8_2428r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2435
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2434 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2438 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2407 p8_2426r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2437
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2436 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2440 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2407 p8_2407l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2439
  intro _
  exact s8_step2438 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2442 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2405r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2441
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2440 hred L1_1 L3_1 L3_2
  intro _
  exact s8_step2425 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2444 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338)
    (L3_2 : Successful q8_2342) :
    SucceedsIn q8_2344 p8_2344l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2443
  intro _
  exact s8_step2442 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2455 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2451r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2454
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2453

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2457 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2449r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2456
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2455 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2460 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2447r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2459
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2458
  intro _
  exact s8_step2457 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2462 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2446r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2461
  intro _
  exact s8_step2460 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2464 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2445r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2463
  intro _
  exact s8_step2462 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2466 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2342 p8_2342l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2465
  intro _
  exact s8_step2464 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2467 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_1908 p8_2341r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2466 hred L1_1 L3_1
  intro L3_2
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2444 hred L1_1 L3_1 L3_2
  intro L3_3
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2404 hred L1_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2475 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2341 p8_2471r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2474
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2473

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2477 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2341 p8_2470r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2476
  intro _
  exact s8_step2475 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2479 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2341 p8_2469r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2478
  intro _
  exact s8_step2477 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2481 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2341 p8_2468r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2480
  intro _
  exact s8_step2479 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_2341 p8_2341l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2482
  intro _
  exact s8_step2481 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2485 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L3_1 : Successful q8_2338) :
    SucceedsIn q8_1908 p8_2339r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2484
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2483 hred L1_1 L3_1
  intro _
  exact s8_step2467 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2501 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2497r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2500
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2499

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2503 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2495r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2502
  intro _
  exact s8_step2501 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2507 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2495 p8_2495l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2506
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2505

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2509 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2493r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2508
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2507 hred L1_1 L4_1
  intro _
  exact s8_step2503 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2511 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2492r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2510
  intro _
  exact s8_step2509 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2521 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2491 p8_2517r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2520
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2523 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2491 p8_2515r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2522
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2521 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2529 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2515 p8_2525r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2528
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2527

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2531 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2515 p8_2515l := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2530
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2529 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2533 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2491 p8_2513r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2532
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2531 hred L1_1 L4_1
  intro _
  exact s8_step2523 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2536 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2491 p8_2491l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2535
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 4 6 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2534
  intro _
  exact s8_step2533 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2547 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2543r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2546
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2545

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2549 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2541r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2548
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2547 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2552 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2539r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2551
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2550
  intro _
  exact s8_step2549 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2554 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2538r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2553
  intro _
  exact s8_step2552 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2556 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2537r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2555
  intro _
  exact s8_step2554 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2558 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2489 p8_2489l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2557
  intro _
  exact s8_step2556 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2559 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2488r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2558 hred L1_1 L4_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2536 hred L1_1 L4_1
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2511 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2569 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2488 p8_2565r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2568
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2567

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2588 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2562 p8_2584r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2587
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2586

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2591 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2562 p8_2582r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2590
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2589
  intro _
  exact s8_step2588 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2592 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2488 p8_2561r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2591 hred L1_1 L4_1
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact h8_2581 hred _
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact h8_2575 hred _
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2569 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2606 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L4_1 : Successful q8_2486) :
    SucceedsIn q8_2338 p8_2486r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.two 1 7 6 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2605
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact h8_2604 hred _
    intro _
    refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact h8_2598 hred _
    intro _
    exact s8_step2592 hred L1_1 L4_1
  intro _
  exact s8_step2559 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2627 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2623r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2626
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2625

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2629 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2621r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2628
  intro _
  exact s8_step2627 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2631 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2619r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2630
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2629 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2633 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2617r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2632
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2631 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2636 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2615r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2635
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2634
  intro _
  exact s8_step2633 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2639 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2613r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2638
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2637
  intro _
  exact s8_step2636 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2649 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2612 p8_2645r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2648
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 5 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2647

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2651 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2612 p8_2643r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2650
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2649 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2654 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2612 p8_2641r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2653
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2652
  intro _
  exact s8_step2651 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2656 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2611r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 1 3 <|
         Hubcap.one 4 2 <|
         Hubcap.one 6 2 <|
         Hubcap.one 7 3 <|
         Hubcap.two 0 5 5 <|
         Hubcap.two 2 3 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2655
    intro _
    exact s8_step2654 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2640
  intro _
  exact s8_step2639 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2658 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2609r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2657
  intro _
  exact s8_step2656 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2675 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2671r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2674
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2673

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2677 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2670r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2676
  intro _
  exact s8_step2675 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2679 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2669r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2678
  intro _
  exact s8_step2677 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2681 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2668r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2680
  intro _
  exact s8_step2679 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2683 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2667r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2682
  intro _
  exact s8_step2681 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2688 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2665 p8_2684r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2687
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2686

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2690 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2665 p8_2665l := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2689
  intro _
  exact s8_step2688 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2691 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2663r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2690 hred L1_1
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2683 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2693 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2662r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2692
  intro _
  exact s8_step2691 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2706 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2702r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2705
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2704

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2708 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2701r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2707
  intro _
  exact s8_step2706 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2710 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2700r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2709
  intro _
  exact s8_step2708 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2712 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2698r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2711
  intro _
  exact s8_step2710 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2719 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2696 p8_2715r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2718
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2717

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2721 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2696 p8_2713r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 7 2 <|
       Hubcap.two 4 6 5 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2720
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2719 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2723 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2695r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 3 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 3 <|
         Hubcap.one 7 2 <|
         Hubcap.two 0 1 7 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2722
    intro _
    exact s8_step2721 hred L1_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2712 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2725 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2661 p8_2694r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2724
  intro _
  exact s8_step2723 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2727 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2660r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 3 <|
         Hubcap.one 3 1 <|
         Hubcap.one 4 2 <|
         Hubcap.one 7 2 <|
         Hubcap.two 0 1 7 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2726
    intro _
    exact s8_step2725 hred L1_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2693 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2729 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2609 p8_2609l := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.two 5 7 6 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2728
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2727 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2731 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_2486 p8_2607r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2730
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s8_step2729 hred L1_1
  intro _
  exact s8_step2658 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2732 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_1908 p8_2337r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s8_step2731 hred L1_1
    intro L4_1
    exact s8_step2606 hred L1_1 L4_1
  intro L3_1
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2485 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2733 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_118 p8_1907r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s8_step2732 hred L1_1
  intro L2_1
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2336 hred L1_1 L2_1
  intro L2_2
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2046 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2734 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116) :
    SucceedsIn q8_1 p8_117r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s8_step2733 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact s8_step1905 hred L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step730 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2767 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756)
    (L2_9 : Successful q8_2762) :
    SucceedsIn q8_116 p8_2764r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2766

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2778 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2762 p8_2774r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2777
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2776

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2780 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2762 p8_2773r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2779
  intro _
  exact s8_step2778 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2782 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2762 p8_2771r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2781
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2780 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2784 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2762 p8_2769r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2783
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2782 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2787 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2762 p8_2762l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2786
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2785
  intro _
  exact s8_step2784 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

end FourColor

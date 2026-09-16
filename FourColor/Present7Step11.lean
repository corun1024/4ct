import FourColor.Present7Step10
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 11 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5258 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5234 p7_5254r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5257

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5264 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5253 p7_5260r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5263
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5262

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5266 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5253 p7_5253l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5265
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5264 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5269 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5252 p7_5252l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5268

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5270 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5208 p7_5233r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact s7_step5269 hred L2_1 L2_2 L3_1
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step5266 hred L2_1 L2_2 L3_1
    intro _
    refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step5258 hred L2_1 L2_2 L3_1
  intro L4_1
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5251 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5275 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5233 p7_5271r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5274

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5277 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5208 p7_5232r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 (-1) <|
         Hubcap.one 5 0 <|
         Hubcap.two 2 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5276
    intro _
    exact s7_step5275 hred L2_1 L2_2 L3_1
  intro _
  exact s7_step5270 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5289 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5232 p7_5285r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5288
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5287

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5291 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5232 p7_5283r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5290
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5289 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5293 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5232 p7_5280r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5292
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5291 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5295 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5232 p7_5278r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5294
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5293 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5297 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5232 p7_5232l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5296
  intro _
  exact s7_step5295 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5298 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_4981 p7_5206r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact s7_step5297 hred L2_1 L2_2 L3_1
    intro _
    exact s7_step5277 hred L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5231 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5310 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5206 p7_5306r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5309
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5308

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5312 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5206 p7_5304r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5311
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5310 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5315 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5206 p7_5302r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5314
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5313
  intro _
  exact s7_step5312 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5317 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5206 p7_5300r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5316
  intro _
  exact s7_step5315 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5336 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5332r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5335
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5334

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5338 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5330r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5337
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5336 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5340 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5328r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5339
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5338 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5343 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5326r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5342
  intro _
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 3 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5341
  intro _
  exact s7_step5340 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5346 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5324r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 3 4 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5345
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5344
  intro _
  exact s7_step5343 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5353 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5322 p7_5349r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5352
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5351

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5355 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5322 p7_5347r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5354
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5353 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5357 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5322 p7_5322l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-2) <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5356
  intro _
  exact s7_step5355 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5359 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5320r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5358
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5357 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5346 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5362 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5299 p7_5299l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5361
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5360
  intro _
  exact s7_step5359 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5363 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5206 p7_5206l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5362 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5318
  intro _
  exact s7_step5317 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5369 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5364) :
    SucceedsIn q7_4980 p7_5365r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5368

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5376 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5364 p7_5372r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5375
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5374

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5387 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5372 p7_5383r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5386
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5385

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5390 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5372 p7_5381r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5389
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5388
  intro _
  exact s7_step5387 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5392 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5372 p7_5379r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 2 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5391
  intro _
  exact s7_step5390 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5394 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5372 p7_5377r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5393
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5392 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5399 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5377 p7_5395r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5398
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5397

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5401 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5377 p7_5377l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5400
  intro _
  exact s7_step5399 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5420 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411)
    (L5_5 : Successful q7_5415)
    (L5_6 : Successful q7_5417) :
    SucceedsIn q7_5370 p7_5417r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5419

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5426 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411)
    (L5_5 : Successful q7_5415) :
    SucceedsIn q7_5417 p7_5422r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5425
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5424

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5429 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411)
    (L5_5 : Successful q7_5415) :
    SucceedsIn q7_5417 p7_5417l := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5428
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5427
  intro _
  exact s7_step5426 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4 L5_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5436 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5415 p7_5432r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5435
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5434

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5439 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5415 p7_5430r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5438
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5437
  intro _
  exact s7_step5436 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5441 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5415 p7_5415l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5440
  intro _
  exact s7_step5439 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5447 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5414 p7_5443r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5446
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5445

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5450 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5414 p7_5414l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5449
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5448
  intro _
  exact s7_step5447 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5451 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5370 p7_5413r := by
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact s7_step5450 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5441 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4
  intro L5_5
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5429 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4 L5_5
  intro L5_6
  exact s7_step5420 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4 L5_5 L5_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5460 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5413 p7_5456r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5459
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5458

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5463 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5413 p7_5454r := by
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5462
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5461
  intro _
  exact s7_step5460 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5466 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5413 p7_5452r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5465
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5464
  intro _
  exact s7_step5463 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5468 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409)
    (L5_4 : Successful q7_5411) :
    SucceedsIn q7_5370 p7_5412r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 (-1) <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5467
    intro _
    exact s7_step5466 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4
  intro _
  exact s7_step5451 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5477 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409) :
    SucceedsIn q7_5411 p7_5473r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5476
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5475

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5479 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409) :
    SucceedsIn q7_5411 p7_5472r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5478
  intro _
  exact s7_step5477 hred L2_1 L2_2 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5482 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409) :
    SucceedsIn q7_5411 p7_5470r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5481
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5480
  intro _
  exact s7_step5479 hred L2_1 L2_2 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5484 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409) :
    SucceedsIn q7_5411 p7_5469r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5483
  intro _
  exact s7_step5482 hred L2_1 L2_2 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5486 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404)
    (L5_3 : Successful q7_5409) :
    SucceedsIn q7_5370 p7_5410r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 (-1) <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5485
    intro _
    exact s7_step5484 hred L2_1 L2_2 L5_1 L5_2 L5_3
  intro L5_4
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5468 hred L2_1 L2_2 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5491 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404) :
    SucceedsIn q7_5409 p7_5487r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5490
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5489

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5493 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404) :
    SucceedsIn q7_5370 p7_5408r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 (-2) <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 3 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5492
    intro _
    exact s7_step5491 hred L2_1 L2_2 L5_1 L5_2
  intro L5_3
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5486 hred L2_1 L2_2 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5495 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402)
    (L5_2 : Successful q7_5404) :
    SucceedsIn q7_5370 p7_5405r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5494
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5493 hred L2_1 L2_2 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5510 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5506r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5509
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5508

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5512 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5505r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5511
  intro _
  exact s7_step5510 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5515 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5503r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5514
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5513
  intro _
  exact s7_step5512 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5518 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5501r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5517
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.two 2 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5516
  intro _
  exact s7_step5515 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5520 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5499r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5519
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5518 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5523 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5497r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5522
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5521
  intro _
  exact s7_step5520 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5536 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5532r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5535
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5534

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5538 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5531r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5537
  intro _
  exact s7_step5536 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5540 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5530r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5539
  intro _
  exact s7_step5538 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5542 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5529r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5541
  intro _
  exact s7_step5540 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5544 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5528r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5543
  intro _
  exact s7_step5542 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5546 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5527r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5545
  intro _
  exact s7_step5544 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5549 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5496 p7_5525r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5548
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5547
  intro _
  exact s7_step5546 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5551 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L5_1 : Successful q7_5402) :
    SucceedsIn q7_5404 p7_5404l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 2 (-1) <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 1 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5550
    intro _
    exact s7_step5549 hred L2_1 L2_2 L5_1
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5524
  intro _
  exact s7_step5523 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5559 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5402 p7_5555r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5558
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5557

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5561 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5402 p7_5553r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5560
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5559 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5573 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5569r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5572
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5571

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5575 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5568r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5574
  intro _
  exact s7_step5573 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5577 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5567r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5576
  intro _
  exact s7_step5575 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5579 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5566r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5578
  intro _
  exact s7_step5577 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5581 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5565r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5580
  intro _
  exact s7_step5579 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5583 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5564r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5582
  intro _
  exact s7_step5581 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5585 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5553 p7_5562r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5584
  intro _
  exact s7_step5583 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5587 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5402 p7_5552r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 3 <|
         Hubcap.one 2 (-2) <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5586
    intro _
    exact s7_step5585 hred L2_1 L2_2
  intro _
  exact s7_step5561 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5598 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5552 p7_5594r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5597
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5596

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5600 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5552 p7_5593r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5599
  intro _
  exact s7_step5598 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5605 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5593 p7_5601r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5604
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5603

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5607 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5552 p7_5592r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 (-2) <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 3 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5606
    intro _
    exact s7_step5605 hred L2_1 L2_2
  intro _
  exact s7_step5600 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5609 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5552 p7_5590r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5608
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5607 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5616 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5590 p7_5612r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5615
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5614

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5618 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5590 p7_5610r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5617
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5616 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5620 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5590 p7_5590l := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5619
  intro _
  exact s7_step5618 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5621 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5402 p7_5402l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact s7_step5620 hred L2_1 L2_2
    intro _
    exact s7_step5609 hred L2_1 L2_2
  intro _
  exact s7_step5587 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5622 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5370 p7_5370l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact s7_step5621 hred L2_1 L2_2
  intro L5_1
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5551 hred L2_1 L2_2 L5_1
  intro L5_2
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5495 hred L2_1 L2_2 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5623 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_5364 p7_5364l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5622 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact s7_step5401 hred L2_1 L2_2
    intro _
    exact s7_step5394 hred L2_1 L2_2
  intro _
  exact s7_step5376 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5624 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978) :
    SucceedsIn q7_877 p7_4979r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact s7_step5623 hred L2_1 L2_2
    intro L3_1
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step5369 hred L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step5363 hred L2_1 L2_2
    intro L3_1
    exact s7_step5298 hred L2_1 L2_2 L3_1
  intro L2_3
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5205 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5638 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L4_1 : Successful q7_5631) :
    SucceedsIn q7_5628 p7_5635r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-4) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5637

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5639 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L4_1 : Successful q7_5631) :
    SucceedsIn q7_5628 p7_5631r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5638 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5648 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5631 p7_5644r := by
  refine succeed_by_split .fan1 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5647
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5646

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5650 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5631 p7_5643r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5649
  intro _
  exact s7_step5648 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5652 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5631 p7_5642r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5651
  intro _
  exact s7_step5650 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5654 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5631 p7_5640r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5653
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5652 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5656 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5628 p7_5630r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 3 <|
         Hubcap.one 2 (-3) <|
         Hubcap.one 3 3 <|
         Hubcap.one 4 3 <|
         Hubcap.two 5 6 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5655
    intro _
    exact s7_step5654 hred L2_1
  intro L4_1
  exact s7_step5639 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5664 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5630 p7_5660r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-3) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5663
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-4) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5662

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5666 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5630 p7_5659r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-4) <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-3) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5665
  intro _
  exact s7_step5664 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5668 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5630 p7_5630l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 (-3) <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-3) <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5667
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5666 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5669 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_4978 p7_5626r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact s7_step5668 hred L2_1
    intro _
    exact s7_step5656 hred L2_1
  intro L3_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5686 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5682r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5685
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5684

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5688 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5681r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5687
  intro _
  exact s7_step5686 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5690 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976) :
    SucceedsIn q7_5626 p7_5680r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5689
  intro _
  exact s7_step5688 hred L2_1

end FourColor

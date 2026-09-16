import FourColor.Present9Hub5

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 6 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3128 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3124r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3127

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3129 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3121r := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact h9_3126 hred _
  intro _
  exact h9_3128 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3130 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3118r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h9_3123 hred _
  intro _
  exact h9_3129 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3131 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2993l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_3120 hred _
  intro _
  exact h9_3130 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3226 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3224l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3225

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3228 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3224r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3227

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3229 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3176l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h9_3226 hred _
  intro _
  exact h9_3228 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3236 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3234l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3235

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3238 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3234r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3237

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3239 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3173l := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_3236 hred _
  intro _
  exact h9_3238 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3268 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3266l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3267

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3270 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3266r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3269

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3271 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3265l := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_3268 hred _
  intro _
  exact h9_3270 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3274 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3272l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3273

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3276 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3272r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3275

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3277 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3265r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h9_3274 hred _
  intro _
  exact h9_3276 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3278 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3264l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_3271 hred _
  intro _
  exact h9_3277 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3280 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3264r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3279

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3281 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3263l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h9_3278 hred _
  intro _
  exact h9_3280 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3284 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3282l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3286 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3282r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3285

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3287 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3263r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h9_3284 hred _
  intro _
  exact h9_3286 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3288 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3170l := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact h9_3281 hred _
  intro _
  exact h9_3287 hred _

end FourColor

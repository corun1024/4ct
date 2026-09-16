import FourColor.Present10Chk1
import FourColor.Present10Chk2
import FourColor.Present10Chk3
import FourColor.Present10Chk4
import FourColor.Present10Chk5
import FourColor.Present10Chk6
import FourColor.Present10Chk7
import FourColor.Present10Chk8
import FourColor.Present10Chk9
import FourColor.Present10Chk10
import FourColor.Present10Chk11
import FourColor.Present10Chk12
import FourColor.Present10Chk13
import FourColor.Present10Chk14
import FourColor.Present10Chk15
import FourColor.Present10Chk16
import FourColor.Present10Chk17
import FourColor.Present10Chk18
import FourColor.Present10Chk19
import FourColor.Present10Chk20
import FourColor.Present10Chk21
import FourColor.Present10Chk22
import FourColor.Present10Chk23
import FourColor.Present10Chk24

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 1 of the arity 10 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_65 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_63l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 6 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_64

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_67 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_63r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 6 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_66

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_68 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_34l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h10_65 hred _
  intro _
  exact h10_67 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_78 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_76l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_77

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_80 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_76r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_79

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_81 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_75l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h10_78 hred _
  intro _
  exact h10_80 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_84 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_82l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_83

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_86 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_82r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_87 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_75r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h10_84 hred _
  intro _
  exact h10_86 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_88 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_74l := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact h10_81 hred _
  intro _
  exact h10_87 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_90 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_74r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_89

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_91 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_73l := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact h10_88 hred _
  intro _
  exact h10_90 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_93 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_73r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_92

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_94 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_31l := by
  refine succeed_by_split .spoke 9 7 true (by decide +kernel) ?_ ?_
  · exact h10_91 hred _
  intro _
  exact h10_93 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_259 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_257l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_258

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_262 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_260l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_261

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_264 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_260r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_263

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_265 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_257r := by
  refine succeed_by_split .spoke 9 7 true (by decide +kernel) ?_ ?_
  · exact h10_262 hred _
  intro _
  exact h10_264 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_266 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_256r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact h10_259 hred _
  intro _
  exact h10_265 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_275 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_273l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_274

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_277 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_273r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_276

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_278 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_272l := by
  refine succeed_by_split .hat 9 6 true (by decide +kernel) ?_ ?_
  · exact h10_275 hred _
  intro _
  exact h10_277 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_281 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_279l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_280

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_283 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_279r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_284 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_272r := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact h10_281 hred _
  intro _
  exact h10_283 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_285 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_271l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact h10_278 hred _
  intro _
  exact h10_284 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_288 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_286l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_287

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_290 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_286r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_289

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_291 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_271r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_288 hred _
  intro _
  exact h10_290 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_292 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_270l := by
  refine succeed_by_split .spoke 9 7 true (by decide +kernel) ?_ ?_
  · exact h10_285 hred _
  intro _
  exact h10_291 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_295 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_293l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_294

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_297 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_293r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_296

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_298 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_270r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_295 hred _
  intro _
  exact h10_297 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_299 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_269l := by
  refine succeed_by_split .hat 9 7 true (by decide +kernel) ?_ ?_
  · exact h10_292 hred _
  intro _
  exact h10_298 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_302 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_300l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_301

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_304 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_300r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_303

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_305 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_269r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_302 hred _
  intro _
  exact h10_304 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_306 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_268l := by
  refine succeed_by_split .spoke 9 8 true (by decide +kernel) ?_ ?_
  · exact h10_299 hred _
  intro _
  exact h10_305 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_309 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_307l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_308

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_311 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_307r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_310

end FourColor

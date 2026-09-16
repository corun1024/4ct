import FourColor.Present11Chk1
import FourColor.Present11Chk2
import FourColor.Present11Chk3
import FourColor.Present11Chk4
import FourColor.Present11Chk5
import FourColor.Present11Chk6

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 1 of the arity 11 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h11_245 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p11_243l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_244

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h11_247 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p11_243r := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_246

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h11_248 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p11_242r := by
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact h11_245 hred _
  intro _
  exact h11_247 hred _

end FourColor

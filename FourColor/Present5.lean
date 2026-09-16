import FourColor.Present5Step1

/-!
Translated from `present5.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Unavoidability for hubs of arity 5

The presentation for hub arity 5: a case analysis on the arities around the
hub, each branch closed by reducibility, by a hubcap, or by a case already
settled.  A mechanical translation of the reference's `present5.v`; see
`FourColor.Present` for the four steps it uses. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
/-- No hub of a minimal counter-example has arity 5. -/
theorem exclude5 : ExcludedArity (RedpartSound theRedpart) 5 := by
  apply exclude_arity
  intro hred
  exact s5_step43 hred

end FourColor

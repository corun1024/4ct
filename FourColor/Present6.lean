import FourColor.Present6Step1

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Unavoidability for hubs of arity 6

The presentation for hub arity 6: a case analysis on the arities around the
hub, each branch closed by reducibility, by a hubcap, or by a case already
settled.  A mechanical translation of the reference's `present6.v`; see
`FourColor.Present` for the four steps it uses. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
/-- No hub of a minimal counter-example has arity 6. -/
theorem exclude6 : ExcludedArity (RedpartSound theRedpart) 6 := by
  apply exclude_arity
  intro hred
  exact s6_step707 hred

end FourColor

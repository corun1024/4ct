import FourColor.Present11Step1

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Unavoidability for hubs of arity 11

The presentation for hub arity 11: a case analysis on the arities around the
hub, each branch closed by reducibility, by a hubcap, or by a case already
settled.  A mechanical translation of the reference's `present11.v`; see
`FourColor.Present` for the four steps it uses. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
/-- No hub of a minimal counter-example has arity 11. -/
theorem exclude11 : ExcludedArity (RedpartSound theRedpart) 11 := by
  apply exclude_arity
  intro hred
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s11_step318 hred
  intro L0_1
  exact s11_step316 hred L0_1

end FourColor

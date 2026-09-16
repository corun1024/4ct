import FourColor.Present8Step10

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Unavoidability for hubs of arity 8

The presentation for hub arity 8: a case analysis on the arities around the
hub, each branch closed by reducibility, by a hubcap, or by a case already
settled.  A mechanical translation of the reference's `present8.v`; see
`FourColor.Present` for the four steps it uses. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
/-- No hub of a minimal counter-example has arity 8. -/
theorem exclude8 : ExcludedArity (RedpartSound theRedpart) 8 := by
  apply exclude_arity
  intro hred
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact s8_step5504 hred
  intro L0_1
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step115 hred L0_1

end FourColor

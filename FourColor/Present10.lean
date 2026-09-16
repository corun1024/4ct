import FourColor.Present10Step3

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Unavoidability for hubs of arity 10

The presentation for hub arity 10: a case analysis on the arities around the
hub, each branch closed by reducibility, by a hubcap, or by a case already
settled.  A mechanical translation of the reference's `present10.v`; see
`FourColor.Present` for the four steps it uses. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
/-- No hub of a minimal counter-example has arity 10. -/
theorem exclude10 : ExcludedArity (RedpartSound theRedpart) 10 := by
  apply exclude_arity
  intro hred
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
    · exact s10_step1113 hred
    intro L1_1
    refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 1 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step413 hred L1_1
  intro L0_1
  exact s10_step13 hred L0_1

end FourColor

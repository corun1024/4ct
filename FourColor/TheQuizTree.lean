import FourColor.CfQuiz
import FourColor.Configurations
import FourColor.QuizData
import FourColor.QuizTreeData
import FourColor.RedPart

/-!
# The quiz tree of the configuration database

Compiling the 633 reducible configurations into a single `QuizTree` lets the
reducibility search do one lookup per triangle of the part it is examining.
This file builds that tree and the reducibility test the presentation scripts
run.

Running `cfquiz` on the configurations is out of reach of the Lean kernel — the
reference has the same problem and solves it with `Eval vm_compute in
cfquiz_tree the_configs`, which Coq accepts in conversion — so `theQuizTree` is
the literal `theQuizTreeLit` of `FourColor.QuizTreeData`, and the work of
identifying that literal with `cfquizTree theConfigs` is split between
`FourColor.QuizData`, which checks the quizzes themselves in blocks, and
`theQuizTreeLit_eq` below, which checks the (cheap) tree insertions.

## Main definitions

* `quizTreeOf` — the quiz tree of a list of quizzes with their symmetry flags.
* `cfquizTree` — the quiz tree of a list of configurations.
* `theQuizTree`, `theRedpart` — the tree of `theConfigs`, and `redpart` on it.

## Main results

* `Hypermap.fit_quizTreeOf`, `Hypermap.fit_cfquizTree` — if the tree fits
  somewhere in a map, then one of the quizzes it holds fits there, in the map
  or in its mirror.
* `theQuizTree_eq` — the literal tree is the tree of `theConfigs`.
* `Hypermap.fit_theQuizTree` — the statement the presentation scripts need.
-/

namespace FourColor

/-- Store a list of quizzes, each with its symmetry flag, one after another.
Storing can only fail by destroying the branching structure of the tree, which
is detected by the shape of the result. -/
def quizTreeRec : QuizTree → List (Quiz × Bool) → QuizTree
  | qt, [] => qt
  | qt, (qz, sym) :: qzs =>
      match QuizTree.storeCfQz qz sym qt with
      | .hubNode t₅₈ t₉ t₁₀ t₁₁ => quizTreeRec (.hubNode t₅₈ t₉ t₁₀ t₁₁) qzs
      | _ => .nil

/-- The quiz tree testing for all the quizzes of `qzs`. -/
def quizTreeOf (qzs : List (Quiz × Bool)) : QuizTree := quizTreeRec QuizTree.empty qzs

/-- Store the quizzes of a list of configurations, one after another. -/
def cfquizTreeRec (qt : QuizTree) (cfs : List Config) : QuizTree :=
  quizTreeRec qt (cfs.map fun cf => (cfquiz cf, cf.sym))

/-- The quiz tree testing for all the configurations of `cfs`. -/
def cfquizTree (cfs : List Config) : QuizTree := cfquizTreeRec QuizTree.empty cfs

/-- The quiz tree of a list of configurations is the quiz tree of their
quizzes. -/
theorem cfquizTree_eq (cfs : List Config) :
    cfquizTree cfs = quizTreeOf (cfs.map fun cf => (cfquiz cf, cf.sym)) := rfl

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

/-- If a tree built from a list of quizzes fits at a dart, then one of those
quizzes is a right quiz that fits somewhere, in the map or in its mirror. -/
theorem fit_quizTreeRec (hp : G.Plain) (hc : G.Cubic) (x : D) :
    ∀ (qzs : List (Quiz × Bool)) (qt : QuizTree), ¬ G.Fit x qt →
      G.Fit x (quizTreeRec qt qzs) →
      ∃ p ∈ qzs, p.1.IsQuizR ∧
        ((∃ y, G.Fitqz y p.1) ∨ ∃ y, G.mirror.Fitqz y p.1) := by
  intro qzs
  induction qzs with
  | nil =>
    intro qt hqt h
    exact absurd h hqt
  | cons p qzs ih =>
    obtain ⟨qz, sym⟩ := p
    intro qt hqt h
    rw [quizTreeRec] at h
    cases hq : QuizTree.storeCfQz qz sym qt with
    | nil => rw [hq] at h; exact absurd h (G.not_fit_nil x)
    | leaf _ _ _ _ => rw [hq] at h; exact absurd h (G.not_fit_nil x)
    | node _ _ _ _ => rw [hq] at h; exact absurd h (G.not_fit_nil x)
    | hubNode t₅₈ t₉ t₁₀ t₁₁ =>
      rw [hq] at h
      by_cases hfit : G.Fit x (QuizTree.storeCfQz qz sym qt)
      · rcases fit_storeCfQz hp hc x qz sym qt hfit with ⟨hqz, hex⟩ | hqt'
        · exact ⟨(qz, sym), List.mem_cons_self, hqz, hex⟩
        · exact absurd hqt' hqt
      · rw [hq] at hfit
        obtain ⟨p', hmem, hp'⟩ := ih _ hfit h
        exact ⟨p', List.mem_cons_of_mem _ hmem, hp'⟩

/-- If the quiz tree of a list of quizzes fits at a dart, then one of them is
found there, in the map or in its mirror. -/
theorem fit_quizTreeOf (hp : G.Plain) (hc : G.Cubic) (x : D) (qzs : List (Quiz × Bool))
    (h : G.Fit x (quizTreeOf qzs)) :
    ∃ p ∈ qzs, p.1.IsQuizR ∧
      ((∃ y, G.Fitqz y p.1) ∨ ∃ y, G.mirror.Fitqz y p.1) :=
  fit_quizTreeRec hp hc x qzs QuizTree.empty (G.not_fit_empty x) h

/-- If a tree built from the configurations fits at a dart, then one of the
configurations it holds is a right quiz that fits somewhere, in the map or in
its mirror. -/
theorem fit_cfquizTreeRec (hp : G.Plain) (hc : G.Cubic) (x : D)
    (cfs : List Config) (qt : QuizTree) (hqt : ¬ G.Fit x qt)
    (h : G.Fit x (cfquizTreeRec qt cfs)) :
    ∃ cf ∈ cfs, (cfquiz cf).IsQuizR ∧
      ((∃ y, G.Fitqz y (cfquiz cf)) ∨ ∃ y, G.mirror.Fitqz y (cfquiz cf)) := by
  obtain ⟨p, hmem, hp⟩ := fit_quizTreeRec hp hc x _ qt hqt h
  obtain ⟨cf, hcf, rfl⟩ := List.mem_map.1 hmem
  exact ⟨cf, hcf, hp⟩

/-- If the quiz tree of a list of configurations fits at a dart, then one of
those configurations is found there, in the map or in its mirror. -/
theorem fit_cfquizTree (hp : G.Plain) (hc : G.Cubic) (x : D) (cfs : List Config)
    (h : G.Fit x (cfquizTree cfs)) :
    ∃ cf ∈ cfs, (cfquiz cf).IsQuizR ∧
      ((∃ y, G.Fitqz y (cfquiz cf)) ∨ ∃ y, G.mirror.Fitqz y (cfquiz cf)) :=
  fit_cfquizTreeRec hp hc x cfs QuizTree.empty (G.not_fit_empty x) h

end Hypermap

set_option maxRecDepth 100000 in
/-- The literal tree of `FourColor.QuizTreeData` is the one `quizTreeOf` builds
from the quizzes: only the tree insertions are checked here, the quizzes
themselves having been checked in `FourColor.QuizData`. -/
theorem theQuizTreeLit_eq : theQuizTreeLit = quizTreeOf theQuizzes := by
  decide +kernel

/-- The quiz tree of the 633 reducible configurations. -/
def theQuizTree : QuizTree := theQuizTreeLit

/-- The tree really is the quiz tree of the configuration database. -/
theorem theQuizTree_eq : theQuizTree = cfquizTree theConfigs := by
  change theQuizTreeLit = cfquizTree theConfigs
  rw [theQuizTreeLit_eq, cfquizTree_eq, theQuizzes_eq]

namespace Hypermap

variable {D : Type*} [Finite D] {G : Hypermap D}

/-- If the quiz tree of the configuration database fits at a dart, then one of
the 633 reducible configurations is found there, in the map or in its mirror. -/
theorem fit_theQuizTree (hp : G.Plain) (hc : G.Cubic) (x : D)
    (h : G.Fit x theQuizTree) :
    ∃ cf ∈ theConfigs, (cfquiz cf).IsQuizR ∧
      ((∃ y, G.Fitqz y (cfquiz cf)) ∨ ∃ y, G.mirror.Fitqz y (cfquiz cf)) :=
  fit_cfquizTree hp hc x theConfigs (theQuizTree_eq ▸ h)

end Hypermap

/-- The reducibility test the presentation scripts run: a part is accepted when
every 2-neighbourhood matching it contains a configuration kernel. -/
def theRedpart : Part → Bool := redpart theQuizTree

end FourColor

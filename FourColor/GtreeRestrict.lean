import FourColor.Ctree
import FourColor.Gtree

/-!
# Restricting a chromogram tree

This is the first phase of a D-reducibility step: the partial chromograms that
match a set of admissible colourings are removed from a `Gtree`.  The result is
a partition of the tree into the deleted and the surviving chromograms, given as
a pair of trees.  The tree is traversed only once, passing down a
`GtreeRestriction`: a list of pairs `(bs, t)`, each standing for the matches
`(bs, et, w)` with `matchpg bs et w` and `et` in the colouring tree `t`.  In the
proof of reducibility this list has size at most 32, and usually at most 8.

## Main definitions

* `GtreeRestriction`, `gtrMem` — sets of trace matches, and the partial
  chromograms they match.
* `gtrCons` — adding a pair to a restriction, dropping empty colouring trees.
* `gsplit r s` — the residual restriction after the symbol `s`, so that a
  restriction can be eliminated like a `Gtree`; `gsplit4` computes all four
  residuals in a single pass.
* `gtrMatch s r` — the test for the one-symbol chromogram `[s]`.
* `Gtree.leafFilter` — the restriction of a leaf to the symbols satisfying a
  predicate.
* `gtreeRestrict t r` — the restriction operation, with its correctness
  theorems `gtreeRestrict_partition` and `mem_fst_gtreeRestrict`.

## References

Gonthier's `theories/proof/gtreerestrict.v`.
-/

namespace FourColor

open Color

/-! ### Restriction sets -/

/-- A set of trace matches to be removed from a chromogram tree.  The pair
`(bs, t)` stands for all matches `(bs, et, w)`, that is, for all traces `et` in
the colouring tree `t` and all partial chromograms `w` with `matchpg bs et w`. -/
abbrev GtreeRestriction := List (List Bool × Ctree)

/-- The restriction `r` contains a match with the partial chromogram `w`. -/
def gtrMem (r : GtreeRestriction) (w : Chromogram) : Bool :=
  r.any fun p => hasMatch p.1 (Ctree.mem p.2) w

/-- The empty restriction matches nothing. -/
@[simp] theorem gtrMem_nil (w : Chromogram) : gtrMem [] w = false := rfl

/-- A match is either with the first pair of the restriction, or with a later one. -/
@[simp] theorem gtrMem_cons (p : List Bool × Ctree) (r : GtreeRestriction)
    (w : Chromogram) :
    gtrMem (p :: r) w = (hasMatch p.1 (Ctree.mem p.2) w || gtrMem r w) := by
  simp [gtrMem]

/-- Nothing matches an empty specification. -/
theorem hasMatch_eq_false {ct : List Color → Bool} (h : ∀ et, ct et = false)
    (bs : List Bool) (w : Chromogram) : hasMatch bs ct w = false := by
  cases hm : hasMatch bs ct w
  · rfl
  · obtain ⟨et, hct, -⟩ := (hasMatch_iff w bs ct).mp hm
    rw [h et] at hct
    simp at hct

/-- `hasMatch` depends on its specification only pointwise. -/
theorem hasMatch_congr {ct ct' : List Color → Bool} (h : ∀ et, ct et = ct' et)
    (bs : List Bool) (w : Chromogram) : hasMatch bs ct w = hasMatch bs ct' w := by
  rw [Bool.eq_iff_iff, hasMatch_iff w bs ct, hasMatch_iff w bs ct']
  simp only [h]

/-- Prefixing a colour to the traces of a colouring tree selects a subtree. -/
theorem hasMatch_ctree_cons (t : Ctree) (e : Color) (bs : List Bool)
    (w : Chromogram) :
    hasMatch bs (fun et => Ctree.mem t (e :: et)) w
      = hasMatch bs (Ctree.mem (t.sel e)) w :=
  hasMatch_congr (fun et => Ctree.mem_cons_eq_mem_sel t e et) bs w

/-- Add the pair `(bs, t)` to `r`, dropping it if `t` is empty. -/
def gtrCons (bs : List Bool) (t : Ctree) (r : GtreeRestriction) : GtreeRestriction :=
  match t with
  | .empty => r
  | _ => (bs, t) :: r

/-- Dropping an empty colouring tree loses no match. -/
@[simp] theorem gtrMem_gtrCons (bs : List Bool) (t : Ctree) (r : GtreeRestriction)
    (w : Chromogram) :
    gtrMem (gtrCons bs t r) w = (hasMatch bs (Ctree.mem t) w || gtrMem r w) := by
  cases t with
  | empty => simp [gtrCons, hasMatch_eq_false (fun et => Ctree.mem_empty et)]
  | node t₁ t₂ t₃ => simp [gtrCons]
  | leaf lf => simp [gtrCons]

/-! ### Splitting off a symbol

Restrictions denote sets of partial chromograms, just as gram trees do, and
`gsplit` lets one eliminate a restriction like a tree: `gsplit r s` represents
exactly the matches of `r` whose chromogram starts with `s`, with that symbol
removed. -/

/-- The contribution of the pair `(bs, t)` to the residual restriction after the
symbol `s`. -/
def gsplitStep : GramSymbol → List Bool → Ctree → GtreeRestriction → GtreeRestriction
  | .push, bs, t, r =>
      gtrCons (false :: bs) (t.sel c2) (gtrCons (true :: bs) (t.sel c3) r)
  | .skip, bs, t, r => gtrCons bs (t.sel c1) r
  | .pop0, [], _, r => r
  | .pop0, false :: bs, t, r => gtrCons bs (t.sel c2) r
  | .pop0, true :: bs, t, r => gtrCons bs (t.sel c3) r
  | .pop1, [], _, r => r
  | .pop1, false :: bs, t, r => gtrCons bs (t.sel c3) r
  | .pop1, true :: bs, t, r => gtrCons bs (t.sel c2) r

/-- The residual restriction after the symbol `s`. -/
def gsplit (r : GtreeRestriction) (s : GramSymbol) : GtreeRestriction :=
  r.foldr (fun p acc => gsplitStep s p.1 p.2 acc) []

/-- Splitting the empty restriction. -/
@[simp] theorem gsplit_nil (s : GramSymbol) : gsplit [] s = [] := rfl

/-- `gsplit` splits the pairs of a restriction one by one. -/
@[simp] theorem gsplit_cons (p : List Bool × Ctree) (r : GtreeRestriction)
    (s : GramSymbol) : gsplit (p :: r) s = gsplitStep s p.1 p.2 (gsplit r s) := rfl

/-- `gsplitStep` accounts for exactly the matches of one pair that begin with the
given symbol. -/
theorem gtrMem_gsplitStep (s : GramSymbol) (bs : List Bool) (t : Ctree)
    (r : GtreeRestriction) (w : Chromogram) :
    gtrMem (gsplitStep s bs t r) w
      = (hasMatch bs (Ctree.mem t) (s :: w) || gtrMem r w) := by
  cases s with
  | push =>
    simp only [gsplitStep, gtrMem_gtrCons, hasMatch, hasMatch_ctree_cons,
      Bool.or_assoc]
  | skip => simp only [gsplitStep, gtrMem_gtrCons, hasMatch, hasMatch_ctree_cons]
  | pop0 =>
    cases bs with
    | nil => simp only [gsplitStep, hasMatch, Bool.false_or]
    | cons b bs =>
      cases b <;>
        simp only [gsplitStep, gtrMem_gtrCons, hasMatch, hasMatch_ctree_cons]
  | pop1 =>
    cases bs with
    | nil => simp only [gsplitStep, hasMatch, Bool.false_or]
    | cons b bs =>
      cases b <;>
        simp only [gsplitStep, gtrMem_gtrCons, hasMatch, hasMatch_ctree_cons]

/-- The defining property of `gsplit`: it removes a leading symbol. -/
@[simp] theorem gtrMem_gsplit (r : GtreeRestriction) (s : GramSymbol)
    (w : Chromogram) : gtrMem (gsplit r s) w = gtrMem r (s :: w) := by
  induction r with
  | nil => rfl
  | cons p r ih => rw [gsplit_cons, gtrMem_gsplitStep, ih, gtrMem_cons]

/-- All four residual restrictions, computed in a single pass. -/
def gsplit4 (r : GtreeRestriction) :
    GtreeRestriction × GtreeRestriction × GtreeRestriction × GtreeRestriction :=
  r.foldr (fun p acc =>
    (gsplitStep .push p.1 p.2 acc.1, gsplitStep .skip p.1 p.2 acc.2.1,
      gsplitStep .pop0 p.1 p.2 acc.2.2.1, gsplitStep .pop1 p.1 p.2 acc.2.2.2))
    ([], [], [], [])

/-- The single pass computes the four residual restrictions.  This is what lets a
restriction be viewed and eliminated as a gram tree. -/
theorem gsplit4_eq (r : GtreeRestriction) :
    gsplit4 r = (gsplit r .push, gsplit r .skip, gsplit r .pop0, gsplit r .pop1) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    change (gsplitStep .push p.1 p.2 (gsplit4 r).1, gsplitStep .skip p.1 p.2 (gsplit4 r).2.1,
      gsplitStep .pop0 p.1 p.2 (gsplit4 r).2.2.1,
      gsplitStep .pop1 p.1 p.2 (gsplit4 r).2.2.2) = _
    simp only [ih, gsplit_cons]

/-! ### Matching a single symbol -/

/-- The pair `(bs, t)` matches the one-symbol chromogram `[s]`. -/
def gtrMatchStep : GramSymbol → List Bool → Ctree → Bool
  | .push, _, t => (t.sel c2).isLeaf || (t.sel c3).isLeaf
  | .skip, _, t => (t.sel c1).isLeaf
  | .pop0, [], _ => false
  | .pop0, false :: _, t => (t.sel c2).isLeaf
  | .pop0, true :: _, t => (t.sel c3).isLeaf
  | .pop1, [], _ => false
  | .pop1, false :: _, t => (t.sel c3).isLeaf
  | .pop1, true :: _, t => (t.sel c2).isLeaf

/-- The matches of `r` contain the one-symbol chromogram `[s]`. -/
def gtrMatch (s : GramSymbol) (r : GtreeRestriction) : Bool :=
  r.any fun p => gtrMatchStep s p.1 p.2

/-- `gtrMatchStep` tests the one-symbol chromograms of a single pair. -/
theorem gtrMatchStep_eq (s : GramSymbol) (bs : List Bool) (t : Ctree) :
    gtrMatchStep s bs t = hasMatch bs (Ctree.mem t) [s] := by
  cases s with
  | push => simp [gtrMatchStep, hasMatch, Ctree.mem_cons_eq_mem_sel]
  | skip => simp [gtrMatchStep, hasMatch, Ctree.mem_cons_eq_mem_sel]
  | pop0 =>
    cases bs with
    | nil => simp [gtrMatchStep, hasMatch]
    | cons b bs => cases b <;> simp [gtrMatchStep, hasMatch, Ctree.mem_cons_eq_mem_sel]
  | pop1 =>
    cases bs with
    | nil => simp [gtrMatchStep, hasMatch]
    | cons b bs => cases b <;> simp [gtrMatchStep, hasMatch, Ctree.mem_cons_eq_mem_sel]

/-- `gtrMatch` tests membership of a one-symbol chromogram. -/
@[simp] theorem gtrMatch_eq (s : GramSymbol) (r : GtreeRestriction) :
    gtrMatch s r = gtrMem r [s] := by
  simp only [gtrMatch, gtrMem, gtrMatchStep_eq]

/-- The matches of `r` spelled out: a pair `(bs, t)` of `r` and a trace of `t`
that matches `w` in the context `bs`. -/
theorem gtrMem_eq_true_iff (r : GtreeRestriction) (w : Chromogram) :
    gtrMem r w = true ↔
      ∃ p ∈ r, ∃ et, Ctree.mem p.2 et = true ∧ matchpg p.1 et w = true := by
  simp [gtrMem, hasMatch_iff]

/-! ### Leaves -/

namespace Gtree

/-- Membership of one-symbol chromograms is `leafMem`. -/
theorem mem_single (t : Gtree) (s : GramSymbol) : mem t [s] = leafMem t s := by
  cases t
  case node t₀ t₁ t₂ t₃ => cases s <;> rfl
  all_goals rfl

/-- A tree that is not a node contains no chromogram of length at least two. -/
theorem mem_cons_cons_of_ne_node {t : Gtree}
    (ht : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) (s s' : GramSymbol)
    (w : Chromogram) : mem t (s :: s' :: w) = false := by
  cases t
  case node t₀ t₁ t₂ t₃ => exact absurd rfl (ht t₀ t₁ t₂ t₃)
  all_goals rfl

/-- The part of a leaf whose symbols satisfy `f`.  Every subset of the symbol
set of a leaf is again the symbol set of a leaf, so this is always defined; on
nodes it returns the empty tree. -/
def leafFilter (f : GramSymbol → Bool) : Gtree → Gtree
  | .leaf0 => if f .push then .leaf0 else .empty
  | .leaf1 => if f .skip then .leaf1 else .empty
  | .leaf2 => if f .pop0 then .leaf2 else .empty
  | .leaf3 => if f .pop1 then .leaf3 else .empty
  | .leaf01 =>
      if f .push then (if f .skip then .leaf01 else .leaf0)
      else (if f .skip then .leaf1 else .empty)
  | .leaf12 =>
      if f .skip then (if f .pop0 then .leaf12 else .leaf1)
      else (if f .pop0 then .leaf2 else .empty)
  | .leaf13 =>
      if f .skip then (if f .pop1 then .leaf13 else .leaf1)
      else (if f .pop1 then .leaf3 else .empty)
  | .leaf23 =>
      if f .pop0 then (if f .pop1 then .leaf23 else .leaf2)
      else (if f .pop1 then .leaf3 else .empty)
  | .node _ _ _ _ => .empty
  | .empty => .empty

/-- `leafFilter` never produces a node. -/
theorem leafFilter_ne_node (f : GramSymbol → Bool) (t t₀ t₁ t₂ t₃ : Gtree) :
    leafFilter f t ≠ .node t₀ t₁ t₂ t₃ := by
  cases t <;> simp only [leafFilter] <;> (try split_ifs) <;> simp

/-- `leafFilter` keeps exactly the symbols of the leaf that satisfy `f`. -/
@[simp] theorem leafMem_leafFilter (f : GramSymbol → Bool) (t : Gtree)
    (s : GramSymbol) : leafMem (leafFilter f t) s = (leafMem t s && f s) := by
  cases t <;> simp only [leafFilter] <;> (try split_ifs) <;> cases s <;>
    simp_all [leafMem]

end Gtree

/-! ### Partitions into a pair of trees -/

/-- Putting the whole tree on the left is a partition. -/
theorem pairPartition_left (t : Gtree) : PairPartition t (t, .empty) := by
  intro w
  cases Gtree.mem t w <;> simp

/-- Putting the whole tree on the right is a partition. -/
theorem pairPartition_right (t : Gtree) : PairPartition t (.empty, t) := by
  intro w
  cases Gtree.mem t w <;> simp

/-- A leaf is partitioned by a predicate on its symbols. -/
theorem pairPartition_leafFilter {t : Gtree}
    (ht : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) (f : GramSymbol → Bool) :
    PairPartition t (t.leafFilter f, t.leafFilter fun s => !f s) := by
  intro w
  rcases w with _ | ⟨s, _ | ⟨s', w⟩⟩
  · simp
  · simp only [Gtree.mem_single, Gtree.leafMem_leafFilter]
    cases Gtree.leafMem t s <;> cases f s <;> simp
  · simp only [Gtree.mem_cons_cons_of_ne_node ht,
      Gtree.mem_cons_cons_of_ne_node (fun a b c d => Gtree.leafFilter_ne_node _ t a b c d)]
    simp

/-- The first component of `consPairs` behaves like a plain node. -/
theorem mem_fst_consPairs {t₀ t₁ t₂ t₃ : Gtree} {p₀ p₁ p₂ p₃ : Gtree × Gtree}
    (h₀ : PairPartition t₀ p₀) (h₁ : PairPartition t₁ p₁) (h₂ : PairPartition t₂ p₂)
    (h₃ : PairPartition t₃ p₃) (w : Chromogram) :
    Gtree.mem (consPairs (.node t₀ t₁ t₂ t₃) p₀ p₁ p₂ p₃).1 w
      = Gtree.mem (.node p₀.1 p₁.1 p₂.1 p₃.1) w := by
  have key : ∀ {t : Gtree} {p : Gtree × Gtree}, PairPartition t p → p.2 = .empty →
      ∀ v : Chromogram, Gtree.mem p.1 v = Gtree.mem t v := by
    intro t p h hp v
    have hv := h v
    rw [hp, Gtree.mem_empty] at hv
    cases hm : Gtree.mem t v <;> rw [hm] at hv <;> simpa using hv
  rw [consPairs]
  split
  · rename_i he
    obtain ⟨hp, -, -, -⟩ := Gtree.empty4_node_iff.mp he
    rw [Gtree.mem_eq_false_of_empty4 he w, hp, Gtree.mem_empty]
  · split
    · rename_i he
      obtain ⟨e₀, e₁, e₂, e₃⟩ := Gtree.empty4_node_iff.mp he
      rcases w with _ | ⟨s, w⟩
      · simp
      · cases s <;> simp only [Gtree.mem_node_cons, Gtree.sel_node_push,
            Gtree.sel_node_skip, Gtree.sel_node_pop0, Gtree.sel_node_pop1]
        · exact (key h₀ e₀ w).symm
        · exact (key h₁ e₁ w).symm
        · exact (key h₂ e₂ w).symm
        · exact (key h₃ e₃ w).symm
    · rfl

/-! ### The restriction operation -/

/-- Restrict the chromogram tree `t` by `r`: the first component of the result
collects the chromograms of `t` that have a match in `r`, and the second one the
remaining chromograms of `t`. -/
def gtreeRestrict : Gtree → GtreeRestriction → Gtree × Gtree
  | .node t₀ t₁ t₂ t₃, [] => (.empty, .node t₀ t₁ t₂ t₃)
  | .node t₀ t₁ t₂ t₃, p :: r =>
      let q := gsplit4 (p :: r)
      consPairs (.node t₀ t₁ t₂ t₃) (gtreeRestrict t₀ q.1) (gtreeRestrict t₁ q.2.1)
        (gtreeRestrict t₂ q.2.2.1) (gtreeRestrict t₃ q.2.2.2)
  | t, r => (t.leafFilter fun s => gtrMatch s r, t.leafFilter fun s => !gtrMatch s r)

/-- Unfolding `gtreeRestrict` at a node, in terms of the residual restrictions. -/
theorem gtreeRestrict_node_cons (t₀ t₁ t₂ t₃ : Gtree) (p : List Bool × Ctree)
    (r : GtreeRestriction) :
    gtreeRestrict (.node t₀ t₁ t₂ t₃) (p :: r)
      = consPairs (.node t₀ t₁ t₂ t₃) (gtreeRestrict t₀ (gsplit (p :: r) .push))
          (gtreeRestrict t₁ (gsplit (p :: r) .skip))
          (gtreeRestrict t₂ (gsplit (p :: r) .pop0))
          (gtreeRestrict t₃ (gsplit (p :: r) .pop1)) := by
  change (fun q => consPairs (.node t₀ t₁ t₂ t₃) (gtreeRestrict t₀ q.1)
      (gtreeRestrict t₁ q.2.1) (gtreeRestrict t₂ q.2.2.1)
      (gtreeRestrict t₃ q.2.2.2)) (gsplit4 (p :: r)) = _
  rw [gsplit4_eq]

/-- Unfolding `gtreeRestrict` at a leaf. -/
theorem gtreeRestrict_of_ne_node {t : Gtree}
    (ht : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) (r : GtreeRestriction) :
    gtreeRestrict t r
      = (t.leafFilter fun s => gtrMatch s r, t.leafFilter fun s => !gtrMatch s r) := by
  cases t
  case node t₀ t₁ t₂ t₃ => exact absurd rfl (ht t₀ t₁ t₂ t₃)
  all_goals rfl

/-- An empty restriction deletes nothing. -/
@[simp] theorem gtreeRestrict_nil (t : Gtree) : gtreeRestrict t [] = (.empty, t) := by
  cases t
  case node t₀ t₁ t₂ t₃ => rfl
  all_goals (rw [gtreeRestrict_of_ne_node (by simp)]; simp [Gtree.leafFilter])

/-- `gtreeRestrict t r` is a partition of `t`. -/
theorem gtreeRestrict_partition (t : Gtree) (r : GtreeRestriction) :
    PairPartition t (gtreeRestrict t r) := by
  induction t generalizing r with
  | node t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    cases r with
    | nil => rw [gtreeRestrict_nil]; exact pairPartition_right _
    | cons p r =>
      rw [gtreeRestrict_node_cons]
      exact consPairs_partition (ih₀ _) (ih₁ _) (ih₂ _) (ih₃ _)
  | _ =>
    rw [gtreeRestrict_of_ne_node (by simp)]
    exact pairPartition_leafFilter (by simp) _

/-- The first component of `gtreeRestrict t r` holds exactly the chromograms of
`t` that have a match in `r`. -/
theorem mem_fst_gtreeRestrict (t : Gtree) (r : GtreeRestriction) (w : Chromogram) :
    Gtree.mem (gtreeRestrict t r).1 w = (Gtree.mem t w && gtrMem r w) := by
  induction t generalizing r w with
  | node t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    cases r with
    | nil => simp
    | cons p r =>
      rw [gtreeRestrict_node_cons,
        mem_fst_consPairs (gtreeRestrict_partition t₀ _) (gtreeRestrict_partition t₁ _)
          (gtreeRestrict_partition t₂ _) (gtreeRestrict_partition t₃ _) w]
      rcases w with _ | ⟨s, w⟩
      · simp
      · cases s <;> simp [ih₀, ih₁, ih₂, ih₃, gtrMem_gsplitStep]
  | _ =>
    rw [gtreeRestrict_of_ne_node (by simp)]
    rcases w with _ | ⟨s, _ | ⟨s', w⟩⟩
    · simp
    · simp only [Gtree.mem_single, Gtree.leafMem_leafFilter, gtrMatch_eq]
    · rw [Gtree.mem_cons_cons_of_ne_node
          (fun a b c d => Gtree.leafFilter_ne_node _ _ a b c d) s s' w,
        Gtree.mem_cons_cons_of_ne_node (by simp) s s' w]
      simp

end FourColor

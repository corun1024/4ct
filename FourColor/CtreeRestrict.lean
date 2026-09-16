import FourColor.Ctree
import FourColor.Gtree

/-!
# Restricting a colouring tree

This is the second phase of a D-reducibility step: the match counts stored in a
`Ctree` are decreased by the number of chromogram matches that the first phase
has just removed, and the colourings whose count falls to zero are split off.
The counts to subtract are passed down as a `CtreeRestriction`: a list of pairs
`(bs, gt)`, each standing for the matches `(bs, et, w)` with `matchpg bs et w`
and `w` in the gram tree `gt`.

The tree is traversed once, the restriction being split by the leading colour at
each level, so that a restriction can be eliminated exactly like a `Ctree` —
both denote multisets of traces.  The result is a pair of trees: the surviving
colourings, whose counts have been decreased, and the colourings that have just
become reachable.

## Main definitions

* `CtreeRestriction`, `ctrSub` — sets of chromogram matches, and the number of
  matches of a partial trace in such a set.
* `ctrCons` — adding a pair to a restriction, dropping empty gram trees.
* `csplit r e` — the residual restriction after the colour `e`.
* `Ctree.decr lf n` — popping `n` leaf constructors, that is, decrementing a
  match count.
* `SctreePartition`, `Ctree.PairPartition` — a pair of trees partitioning a
  tree.
* `Ctree.leafPair`, `Ctree.consPairs` — the pair constructors for the base and
  the inductive step of the restriction.
* `Ctree.restrict h t r` — the restriction operation, with its correctness
  theorem `Ctree.restrict_correct`.

## References

Gonthier's `theories/proof/ctreerestrict.v`.
-/

namespace FourColor

open Color

/-! ### Match counts in a gram tree

A gram tree that is not a node holds only one-symbol chromograms, so it has no
match with a trace of two or more colours; and the matches of a longer trace in
a node are those of its subtrees. -/

namespace Gtree

/-- Only nodes hold chromograms of length two or more. -/
theorem mem_eq_false_of_two_le {t : Gtree}
    (hn : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) {w : Chromogram} (hw : 2 ≤ w.length) :
    Gtree.mem t w = false := by
  match w with
  | [] => simp
  | [_] => simp at hw
  | _ :: _ :: _ => cases t <;> first | rfl | exact absurd rfl (hn _ _ _ _)

/-- A gram tree that is not a node has no match with a trace of length two or
more. -/
theorem sub_eq_zero_of_two_le {t : Gtree}
    (hn : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) (bs : List Bool) {et : List Color}
    (het : 2 ≤ et.length) : Gtree.sub t bs et = 0 := by
  by_contra hne
  obtain ⟨w, hw, hm⟩ := (matchCount_ne_zero_iff et (Gtree.mem t) bs).mp hne
  rw [mem_eq_false_of_two_le hn (by rw [matchpg_length et bs w hm]; exact het)] at hw
  exact Bool.noConfusion hw

/-- Matching under a leading symbol is matching in the corresponding subtree. -/
private theorem matchCount_mem_node_cons (t₀ t₁ t₂ t₃ : Gtree) (s : GramSymbol)
    (bs : List Bool) (et : List Color) :
    matchCount (fun w => Gtree.mem (.node t₀ t₁ t₂ t₃) (s :: w)) bs et
      = matchCount (Gtree.mem (Gtree.sel (.node t₀ t₁ t₂ t₃) s)) bs et :=
  matchCount_congr et _ _ bs fun _ => rfl

@[simp] theorem sub_node_c1 (t₀ t₁ t₂ t₃ : Gtree) (bs : List Bool) (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) bs (c1 :: et) = Gtree.sub t₁ bs et := by
  simp only [Gtree.sub, matchCount_c1, matchCount_mem_node_cons, sel_node_skip]

@[simp] theorem sub_node_c2_nil (t₀ t₁ t₂ t₃ : Gtree) (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) [] (c2 :: et) = Gtree.sub t₀ [false] et := by
  simp only [Gtree.sub, matchCount_c2_nil, matchCount_mem_node_cons, sel_node_push]

@[simp] theorem sub_node_c2_false (t₀ t₁ t₂ t₃ : Gtree) (bs : List Bool)
    (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) (false :: bs) (c2 :: et)
      = Gtree.sub t₀ (false :: false :: bs) et + Gtree.sub t₂ bs et := by
  simp only [Gtree.sub, matchCount_c2_false, matchCount_mem_node_cons, sel_node_push,
    sel_node_pop0]

@[simp] theorem sub_node_c2_true (t₀ t₁ t₂ t₃ : Gtree) (bs : List Bool)
    (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) (true :: bs) (c2 :: et)
      = Gtree.sub t₀ (false :: true :: bs) et + Gtree.sub t₃ bs et := by
  simp only [Gtree.sub, matchCount_c2_true, matchCount_mem_node_cons, sel_node_push,
    sel_node_pop1]

@[simp] theorem sub_node_c3_nil (t₀ t₁ t₂ t₃ : Gtree) (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) [] (c3 :: et) = Gtree.sub t₀ [true] et := by
  simp only [Gtree.sub, matchCount_c3_nil, matchCount_mem_node_cons, sel_node_push]

@[simp] theorem sub_node_c3_false (t₀ t₁ t₂ t₃ : Gtree) (bs : List Bool)
    (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) (false :: bs) (c3 :: et)
      = Gtree.sub t₀ (true :: false :: bs) et + Gtree.sub t₃ bs et := by
  simp only [Gtree.sub, matchCount_c3_false, matchCount_mem_node_cons, sel_node_push,
    sel_node_pop1]

@[simp] theorem sub_node_c3_true (t₀ t₁ t₂ t₃ : Gtree) (bs : List Bool)
    (et : List Color) :
    Gtree.sub (.node t₀ t₁ t₂ t₃) (true :: bs) (c3 :: et)
      = Gtree.sub t₀ (true :: true :: bs) et + Gtree.sub t₂ bs et := by
  simp only [Gtree.sub, matchCount_c3_true, matchCount_mem_node_cons, sel_node_push,
    sel_node_pop0]

@[simp] theorem sub_zero_cons (t : Gtree) (bs : List Bool) (et : List Color) :
    Gtree.sub t bs ((0 : Color) :: et) = 0 := rfl

@[simp] theorem sub_trace_nil (t : Gtree) (bs : List Bool) : Gtree.sub t bs [] = 0 := by
  simp [Gtree.sub]

end Gtree

/-! ### Restriction sets -/

/-- A set of chromogram matches to be removed from a colouring tree.  The pair
`(bs, gt)` stands for all matches `(bs, et, w)`, that is, for all partial
chromograms `w` in the gram tree `gt` and all traces `et` with
`matchpg bs et w`. -/
abbrev CtreeRestriction := List (List Bool × Gtree)

/-- Add the pair `(bs, t)` to `r`, dropping it if `t` is empty. -/
def ctrCons (bs : List Bool) (t : Gtree) (r : CtreeRestriction) : CtreeRestriction :=
  match t with
  | .empty => r
  | _ => (bs, t) :: r

/-- The number of matches of the partial trace `et` in the restriction `r`. -/
def ctrSub (r : CtreeRestriction) (et : List Color) : ℕ :=
  (r.map fun p => Gtree.sub p.2 p.1 et).sum

@[simp] theorem ctrSub_nil (et : List Color) : ctrSub [] et = 0 := rfl

@[simp] theorem ctrSub_cons (p : List Bool × Gtree) (r : CtreeRestriction)
    (et : List Color) : ctrSub (p :: r) et = Gtree.sub p.2 p.1 et + ctrSub r et := by
  simp [ctrSub]

@[simp] theorem ctrSub_append (r₁ r₂ : CtreeRestriction) (et : List Color) :
    ctrSub (r₁ ++ r₂) et = ctrSub r₁ et + ctrSub r₂ et := by simp [ctrSub]

@[simp] theorem ctrSub_ctrCons (bs : List Bool) (t : Gtree) (r : CtreeRestriction)
    (et : List Color) :
    ctrSub (ctrCons bs t r) et = Gtree.sub t bs et + ctrSub r et := by
  cases t <;> simp [ctrCons]

/-- No match has an empty trace: a match of `et` has a chromogram of the same
length, and gram trees contain no empty chromogram. -/
@[simp] theorem ctrSub_trace_nil (r : CtreeRestriction) : ctrSub r [] = 0 := by
  induction r with
  | nil => rfl
  | cons p r ih => simp [ih]

/-! ### Splitting off a colour

A restriction denotes a multiset of traces, just as a colouring tree does, and
`csplit` lets one eliminate a restriction like a tree: `csplit r e` represents
exactly the matches of `r` whose trace starts with `e`, with that colour
removed. -/

/-- The contribution of the pair `(bs, t)` to the restriction split off by the
colour `e`. -/
def csplitStep (e : Color) (bs : List Bool) (t : Gtree)
    (r : CtreeRestriction) : CtreeRestriction :=
  match t with
  | .node t₀ t₁ t₂ t₃ =>
    match e, bs with
    | .c0, _ => r
    | .c1, _ => ctrCons bs t₁ r
    | .c2, [] => ctrCons [false] t₀ r
    | .c2, false :: bs' => ctrCons (false :: false :: bs') t₀ (ctrCons bs' t₂ r)
    | .c2, true :: bs' => ctrCons (false :: true :: bs') t₀ (ctrCons bs' t₃ r)
    | .c3, [] => ctrCons [true] t₀ r
    | .c3, false :: bs' => ctrCons (true :: false :: bs') t₀ (ctrCons bs' t₃ r)
    | .c3, true :: bs' => ctrCons (true :: true :: bs') t₀ (ctrCons bs' t₂ r)
  | _ => r

/-- The residual restriction after the colour `e`: the matches of `r` whose
trace starts with `e`, with that colour removed.  Matches whose trace is just
`[e]` are dropped, so `csplit` is faithful only where at least one further
colour follows — which is where the restriction of a tree uses it. -/
def csplit (r : CtreeRestriction) (e : Color) : CtreeRestriction :=
  r.foldr (fun p acc => csplitStep e p.1 p.2 acc) []

@[simp] theorem csplit_nil (e : Color) : csplit [] e = [] := rfl

@[simp] theorem csplit_cons (p : List Bool × Gtree) (r : CtreeRestriction) (e : Color) :
    csplit (p :: r) e = csplitStep e p.1 p.2 (csplit r e) := rfl

/-- Nothing but a node contributes to a split. -/
private theorem csplitStep_of_not_node {t : Gtree}
    (hn : ∀ t₀ t₁ t₂ t₃, t ≠ .node t₀ t₁ t₂ t₃) (e : Color) (bs : List Bool)
    (r : CtreeRestriction) : csplitStep e bs t r = r := by
  cases t <;> first | rfl | exact absurd rfl (hn _ _ _ _)

theorem ctrSub_csplitStep (e e' : Color) (et : List Color) (bs : List Bool) (t : Gtree)
    (r : CtreeRestriction) :
    ctrSub (csplitStep e bs t r) (e' :: et)
      = Gtree.sub t bs (e :: e' :: et) + ctrSub r (e' :: et) := by
  by_cases hnode : ∃ t₀ t₁ t₂ t₃, t = Gtree.node t₀ t₁ t₂ t₃
  · obtain ⟨t₀, t₁, t₂, t₃, rfl⟩ := hnode
    cases e
    · simp [csplitStep]
    · simp [csplitStep]
    · cases bs with
      | nil => simp [csplitStep]
      | cons b bs => cases b <;> simp [csplitStep] <;> omega
    · cases bs with
      | nil => simp [csplitStep]
      | cons b bs => cases b <;> simp [csplitStep] <;> omega
  · have hn : ∀ t₀ t₁ t₂ t₃, t ≠ Gtree.node t₀ t₁ t₂ t₃ := fun a b c d h =>
      hnode ⟨a, b, c, d, h⟩
    rw [csplitStep_of_not_node hn, Gtree.sub_eq_zero_of_two_le hn bs (by simp)]
    simp

/-- The defining property of `csplit`: it removes a leading colour. -/
theorem ctrSub_csplit (r : CtreeRestriction) (e e' : Color) (et : List Color) :
    ctrSub (csplit r e) (e' :: et) = ctrSub r (e :: e' :: et) := by
  induction r with
  | nil => simp
  | cons p r ih => rw [csplit_cons, ctrSub_csplitStep, ih, ctrSub_cons]

/-! ### Decrementing a match count -/

namespace Ctree

/-- Pop `n` leaf constructors off `lf`, that is, decrease a match count by
`n`. -/
def decr : Ctree → ℕ → Ctree
  | .leaf lf, n + 1 => decr lf n
  | t, _ => t

@[simp] theorem decr_zero (t : Ctree) : decr t 0 = t := by cases t <;> rfl

@[simp] theorem decr_leaf_succ (lf : Ctree) (n : ℕ) :
    decr (.leaf lf) (n + 1) = decr lf n := rfl

@[simp] theorem decr_empty (n : ℕ) : decr .empty n = .empty := by cases n <;> rfl

@[simp] theorem decr_node (t₁ t₂ t₃ : Ctree) (n : ℕ) :
    decr (.node t₁ t₂ t₃) n = .node t₁ t₂ t₃ := by cases n <;> rfl

@[simp] theorem leafOf_zero : leafOf 0 = .empty := rfl

@[simp] theorem isEmpty_leafOf (n : ℕ) : isEmpty (leafOf n) = (n == 0) := by
  cases n <;> rfl

@[simp] theorem decr_leafOf (m n : ℕ) : decr (leafOf m) n = leafOf (m - n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih => cases m with
    | zero => simp
    | succ m => simpa [leafOf] using ih m

/-- A tree that is not a leaf holds no count to decrease. -/
theorem decr_of_not_isLeaf {t : Ctree} (h : isLeaf t = false) (n : ℕ) : decr t n = t := by
  cases t <;> simp_all

@[simp] theorem isLeaf_leafOf (n : ℕ) : isLeaf (leafOf n) = decide (n ≠ 0) := by
  cases n <;> simp [leafOf]

@[simp] theorem sel_leafOf (n : ℕ) (e : Color) : sel (leafOf n) e = .empty := by
  cases n <;> rfl

@[simp] theorem mem_leafOf_cons (n : ℕ) (e : Color) (et : List Color) :
    mem (leafOf n) (e :: et) = false := by simp [mem]

/-- A proper leaf is the canonical leaf of its own count. -/
theorem eq_leafOf_of_proper_zero : ∀ {lf : Ctree}, Proper 0 lf → lf = leafOf (sub lf []) := by
  intro lf
  induction lf with
  | node _ _ _ _ _ _ => exact fun h => absurd h not_false
  | leaf l ih =>
    intro h
    conv_lhs => rw [ih h]
    rfl
  | empty => intro _; rfl

/-- A proper tree of positive height has no empty trace. -/
theorem sub_nil_eq_zero_of_proper_succ {h : ℕ} {t : Ctree} (ht : Proper (h + 1) t) :
    sub t [] = 0 := by
  cases t with
  | node _ _ _ => rfl
  | leaf _ => exact absurd ht not_false
  | empty => rfl

/-! ### Partitions -/

end Ctree

/-- `st'` and `st''` partition `st`: they are exclusive, and their union is
`st`.  Match counts need not add up. -/
def SctreePartition (st st' st'' : List Color → Bool) : Prop :=
  ∀ et, if st et then st' et ≠ st'' et else st' et = false ∧ st'' et = false

namespace Ctree

/-- A pair of trees partitions a tree. -/
def PairPartition (t : Ctree) (p : Ctree × Ctree) : Prop :=
  SctreePartition (Ctree.mem t) (Ctree.mem p.1) (Ctree.mem p.2)

/-- An untouched tree is partitioned by itself and the empty tree. -/
theorem pairPartition_empty (t : Ctree) : PairPartition t (t, .empty) := by
  intro et
  split <;> simp_all

/-- The empty tree is partitioned by two empty trees. -/
theorem pairPartition_empty_empty : PairPartition .empty (.empty, .empty) := by
  intro et; simp

/-! ### The pair constructors -/

/-- Assemble three restriction pairs into one, componentwise. -/
def consPairs (p₁ p₂ p₃ : Ctree × Ctree) : Ctree × Ctree :=
  (cons p₁.1 p₂.1 p₃.1, cons p₁.2 p₂.2 p₃.2)

/-- The pair partitioning `cons lf₁ lf₂ lf₃`, given the decremented leaves
`lf₁' lf₂' lf₃'`: the second component keeps the branches whose count has fallen
to zero. -/
def leafPair (lf₁ lf₂ lf₃ lf₁' lf₂' lf₃' : Ctree) : Ctree × Ctree :=
  (cons lf₁' lf₂' lf₃',
    cons (if lf₁'.isEmpty then lf₁ else .empty) (if lf₂'.isEmpty then lf₂ else .empty)
      (if lf₃'.isEmpty then lf₃ else .empty))

/-- `leafPair` is `consPairs` of its three branches. -/
theorem leafPair_eq_consPairs (lf₁ lf₂ lf₃ lf₁' lf₂' lf₃' : Ctree) :
    leafPair lf₁ lf₂ lf₃ lf₁' lf₂' lf₃'
      = consPairs (lf₁', if lf₁'.isEmpty then lf₁ else .empty)
          (lf₂', if lf₂'.isEmpty then lf₂ else .empty)
          (lf₃', if lf₃'.isEmpty then lf₃ else .empty) := rfl

/-- Partitions of the subtrees assemble into a partition of a node. -/
theorem consPairs_partition {t₁ t₂ t₃ : Ctree} {p₁ p₂ p₃ : Ctree × Ctree}
    (h₁ : PairPartition t₁ p₁) (h₂ : PairPartition t₂ p₂) (h₃ : PairPartition t₃ p₃) :
    PairPartition (.node t₁ t₂ t₃) (consPairs p₁ p₂ p₃) := by
  intro et
  cases et with
  | nil => simp [consPairs]
  | cons e et =>
    cases e <;>
      simp only [consPairs, mem_cons_eq_mem_sel, sel_cons, sel_node_c1, sel_node_c2,
        sel_node_c3, c0_eq_zero, sel_zero, mem_empty] <;>
      first | exact h₁ et | exact h₂ et | exact h₃ et | simp

/-- A branch of the base case: decreasing the count `n` by `m` moves the branch
to the second component exactly when the count reaches zero. -/
theorem pairPartition_leafOf (n m : ℕ) :
    PairPartition (leafOf n)
      (leafOf (n - m), if isEmpty (leafOf (n - m)) then leafOf n else .empty) := by
  by_cases hk : n - m = 0
  · have h₂ : (if isEmpty (leafOf (n - m)) then leafOf n else Ctree.empty) = leafOf n := by
      simp [hk, isEmpty]
    rw [h₂, hk, leafOf_zero]
    intro et
    split <;> simp_all
  · have h₂ : (if isEmpty (leafOf (n - m)) then leafOf n else Ctree.empty)
        = Ctree.empty := by simp [hk]
    rw [h₂]
    intro et
    cases et with
    | nil =>
      simp only [mem_nil, isLeaf_leafOf, decide_not]
      have hn : n ≠ 0 := by omega
      simp [hn, hk]
    | cons e et => simp

/-! ### The restriction -/

/-- Subtract the match counts of the restriction `r` from those of the proper
tree `t` of height `h + 1`.  The first component of the result holds the
surviving colourings, the second the ones whose count has fallen to zero. -/
def restrict (h : ℕ) (t : Ctree) (r : CtreeRestriction) : Ctree × Ctree :=
  match r with
  | [] => (t, .empty)
  | _ :: _ =>
    match h, t with
    | 0, .node lf₁ lf₂ lf₃ =>
        leafPair lf₁ lf₂ lf₃ (lf₁.decr (ctrSub r [c1])) (lf₂.decr (ctrSub r [c2]))
          (lf₃.decr (ctrSub r [c3]))
    | h + 1, .node t₁ t₂ t₃ =>
        consPairs (restrict h t₁ (csplit r c1)) (restrict h t₂ (csplit r c2))
          (restrict h t₃ (csplit r c3))
    | _, _ => (.empty, .empty)

@[simp] theorem restrict_nil (h : ℕ) (t : Ctree) : restrict h t [] = (t, .empty) := by
  cases h <;> cases t <;> rfl

theorem restrict_zero_node (lf₁ lf₂ lf₃ : Ctree) {r : CtreeRestriction} (hr : r ≠ []) :
    restrict 0 (.node lf₁ lf₂ lf₃) r
      = leafPair lf₁ lf₂ lf₃ (lf₁.decr (ctrSub r [c1])) (lf₂.decr (ctrSub r [c2]))
          (lf₃.decr (ctrSub r [c3])) := by
  cases r with
  | nil => exact absurd rfl hr
  | cons p r => rfl

theorem restrict_succ_node (h : ℕ) (t₁ t₂ t₃ : Ctree) {r : CtreeRestriction}
    (hr : r ≠ []) :
    restrict (h + 1) (.node t₁ t₂ t₃) r
      = consPairs (restrict h t₁ (csplit r c1)) (restrict h t₂ (csplit r c2))
          (restrict h t₃ (csplit r c3)) := by
  cases r with
  | nil => exact absurd rfl hr
  | cons p r => rfl

@[simp] theorem restrict_empty (h : ℕ) (r : CtreeRestriction) :
    restrict h .empty r = (.empty, .empty) := by
  cases r <;> cases h <;> rfl

/-- The inductive step for match counts: a subtree whose counts are those of `T`
less those of the split restriction has the counts of `T` under a leading colour
less those of the whole restriction. -/
private theorem sub_sub_ctrSub_cons {h : ℕ} {T P : Ctree} {r : CtreeRestriction}
    {e : Color} (hT : Proper (h + 1) T)
    (hP : ∀ et, sub P et = sub T et - ctrSub (csplit r e) et) (et : List Color) :
    sub P et = sub T et - ctrSub r (e :: et) := by
  cases et with
  | nil => rw [hP, ctrSub_trace_nil, sub_nil_eq_zero_of_proper_succ hT]; simp
  | cons e' et' => rw [hP, ctrSub_csplit]

/-- The restriction of a tree of height `h + 1` is a partition of it whose first
component has the match counts of `t` decreased by those of `r`. -/
theorem restrict_correct : ∀ (h : ℕ) (t : Ctree) (r : CtreeRestriction),
    Proper (h + 1) t →
    Proper (h + 1) (restrict h t r).1 ∧ Proper (h + 1) (restrict h t r).2 ∧
      PairPartition t (restrict h t r) ∧
      ∀ et, sub (restrict h t r).1 et = sub t et - ctrSub r et := by
  intro h
  induction h with
  | zero =>
    intro t r ht
    rcases r with _ | ⟨p, r⟩
    · exact ⟨ht, trivial, pairPartition_empty t, fun et => by simp⟩
    cases t with
    | leaf _ => exact absurd ht not_false
    | empty =>
      refine ⟨trivial, trivial, ?_, fun et => by simp⟩
      rw [restrict_empty]; exact pairPartition_empty_empty
    | node lf₁ lf₂ lf₃ =>
      obtain ⟨-, hp₁, hp₂, hp₃⟩ := ht
      obtain ⟨n₁, rfl⟩ : ∃ n, lf₁ = leafOf n := ⟨_, eq_leafOf_of_proper_zero hp₁⟩
      obtain ⟨n₂, rfl⟩ : ∃ n, lf₂ = leafOf n := ⟨_, eq_leafOf_of_proper_zero hp₂⟩
      obtain ⟨n₃, rfl⟩ : ∃ n, lf₃ = leafOf n := ⟨_, eq_leafOf_of_proper_zero hp₃⟩
      rw [restrict_zero_node _ _ _ (by simp), leafPair_eq_consPairs]
      simp only [decr_leafOf, consPairs]
      refine ⟨cons_proper (proper_leafOf _) (proper_leafOf _) (proper_leafOf _), ?_, ?_, ?_⟩
      · refine cons_proper ?_ ?_ ?_ <;> split <;>
          first | exact proper_leafOf _ | trivial
      · exact consPairs_partition (pairPartition_leafOf n₁ _) (pairPartition_leafOf n₂ _)
          (pairPartition_leafOf n₃ _)
      · intro et
        cases et with
        | nil => simp
        | cons e et =>
          cases et with
          | nil => cases e <;> simp [sub_leafOf]
          | cons e' et' => cases e <;> simp
  | succ h ih =>
    intro t r ht
    rcases r with _ | ⟨p, r⟩
    · exact ⟨ht, trivial, pairPartition_empty t, fun et => by simp⟩
    cases t with
    | leaf _ => exact absurd ht not_false
    | empty =>
      refine ⟨trivial, trivial, ?_, fun et => by simp⟩
      rw [restrict_empty]; exact pairPartition_empty_empty
    | node t₁ t₂ t₃ =>
      obtain ⟨-, hp₁, hp₂, hp₃⟩ := ht
      obtain ⟨q₁, q₂, q₃, q₄⟩ := ih t₁ (csplit (p :: r) c1) hp₁
      obtain ⟨s₁, s₂, s₃, s₄⟩ := ih t₂ (csplit (p :: r) c2) hp₂
      obtain ⟨u₁, u₂, u₃, u₄⟩ := ih t₃ (csplit (p :: r) c3) hp₃
      rw [restrict_succ_node _ _ _ _ (by simp)]
      simp only [consPairs]
      refine ⟨cons_proper q₁ s₁ u₁, cons_proper q₂ s₂ u₂, ?_, ?_⟩
      · exact consPairs_partition q₃ s₃ u₃
      · intro et
        cases et with
        | nil => simp
        | cons e et =>
          rw [sub_cons, sub_cons_eq_sub_sel, sub_cons_eq_sub_sel]
          cases e
          · simp
          · exact sub_sub_ctrSub_cons hp₁ q₄ et
          · exact sub_sub_ctrSub_cons hp₂ s₄ et
          · exact sub_sub_ctrSub_cons hp₃ u₄ et

/-- The two components of a restriction are proper trees of the same height. -/
theorem restrict_proper {h : ℕ} {t : Ctree} (r : CtreeRestriction)
    (ht : Proper (h + 1) t) :
    Proper (h + 1) (restrict h t r).1 ∧ Proper (h + 1) (restrict h t r).2 :=
  ⟨(restrict_correct h t r ht).1, (restrict_correct h t r ht).2.1⟩

/-- A restriction partitions the tree it is applied to. -/
theorem restrict_partition {h : ℕ} {t : Ctree} (r : CtreeRestriction)
    (ht : Proper (h + 1) t) : PairPartition t (restrict h t r) :=
  (restrict_correct h t r ht).2.2.1

/-- The surviving match counts are the original ones less those of the
restriction. -/
theorem sub_fst_restrict {h : ℕ} {t : Ctree} (r : CtreeRestriction)
    (ht : Proper (h + 1) t) (et : List Color) :
    sub (restrict h t r).1 et = sub t et - ctrSub r et :=
  (restrict_correct h t r ht).2.2.2 et

end Ctree

end FourColor

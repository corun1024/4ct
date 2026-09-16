import FourColor.CtreeRestrict
import FourColor.GtreeRestrict
import FourColor.InitCtree
import FourColor.InitGtree
import FourColor.Chromogram

/-!
# The Kempe closure tree

The reducibility steps put together: the Kempe closure tree of a configuration
is the set of even ring-trace colourings in the Kempe co-closure of the traces
its map admits.  It is computed by alternately restricting a colouring tree by
the chromograms still available and a gram tree by the colourings still
available, until the two stabilise.

## Main definitions

* `Ctree.size` — the number of traces a colouring tree holds.
* `kempeStep`, `kempeStep2c`, `kempeTreeClosure` — the closure loop.
* `KempeValid`, `KempeComplete` — the loop invariant and the progress predicate.
* `KtcCorrect` — correctness of an approximation of the loop.
* `kempeTreeOf`, `kempeTreeAt` — the Kempe closure tree of a restriction tree.

## Main results

* `Ctree.size_of_pairPartition` — a partition splits the size additively.
* `Ctree.size_eq_zero` — a proper tree of size zero is empty.
* `Ctree.size_le` — a proper tree of height `h` holds at most `3 ^ h` traces.
* `kempeStep_correct` — the reference's `IHstep`: one improvement step preserves
  validity and improves the progress bound.
* `kempeTreeClosure_correct` — the reference's `Kempe_tree_closure_correct`.
* `kempeValid_init`, `kempeComplete_init`, `kempeValid_restrict` — the initial
  state of the loop is valid and accounts for every trace.
* `kempeCoclosure_of_not_mem`, `not_mem_iff_kempeCoclosure` — the reference's
  `Kempe_validP` and `Kempe_completeP`.
* `not_mem_kempeTreeOf_iff`, `not_mem_kempeTreeAt_iff` — the reference's
  `Kempe_treeP`, for an arbitrary restriction tree.
-/

namespace FourColor

namespace Ctree

/-- The number of traces a colouring tree holds. -/
def size : Ctree → ℕ
  | .node t₁ t₂ t₃ => size t₁ + (size t₂ + size t₃)
  | .leaf _ => 1
  | .empty => 0

@[simp] theorem size_empty : size .empty = 0 := rfl

@[simp] theorem size_leaf (t : Ctree) : size (.leaf t) = 1 := rfl

@[simp] theorem size_node (t₁ t₂ t₃ : Ctree) :
    size (.node t₁ t₂ t₃) = size t₁ + (size t₂ + size t₃) := rfl

/-- A tree with no members is empty. -/
theorem size_eq_zero_of_not_mem : ∀ {t : Ctree}, (∀ et, mem t et = false) → size t = 0
  | .empty, _ => rfl
  | .leaf _, h => by simpa using h []
  | .node t₁ t₂ t₃, h => by
    have h₁ : ∀ et, mem t₁ et = false := fun et => h (Color.c1 :: et)
    have h₂ : ∀ et, mem t₂ et = false := fun et => h (Color.c2 :: et)
    have h₃ : ∀ et, mem t₃ et = false := fun et => h (Color.c3 :: et)
    rw [size_node, size_eq_zero_of_not_mem h₁, size_eq_zero_of_not_mem h₂,
      size_eq_zero_of_not_mem h₃]

/-- Only a leaf holds the empty trace. -/
theorem eq_leaf_of_mem_nil : ∀ {t : Ctree}, mem t [] = true → ∃ lf, t = .leaf lf
  | .leaf lf, _ => ⟨lf, rfl⟩
  | .node _ _ _, h => by simp at h
  | .empty, h => by simp at h

/-- A partition splits the size additively. -/
theorem size_of_pairPartition : ∀ {t t' t'' : Ctree}, PairPartition t (t', t'') →
    size t = size t' + size t'' := by
  intro t
  induction t with
  | empty =>
    intro t' t'' hp
    have h' : ∀ et, mem t' et = false := fun et => by simpa using (hp et).1
    have h'' : ∀ et, mem t'' et = false := fun et => by simpa using (hp et).2
    rw [size_empty, size_eq_zero_of_not_mem h', size_eq_zero_of_not_mem h'']
  | leaf lf _ =>
    intro t' t'' hp
    have hmemnil : mem (.leaf lf) [] = true := by simp [mem, sub]
    have hnil := hp []
    rw [ite_eq_left hmemnil] at hnil
    have hcons : ∀ (e : Color) (et : List Color),
        mem t' (e :: et) = false ∧ mem t'' (e :: et) = false := by
      intro e et
      have h := hp (e :: et)
      rwa [ite_eq_right (by simp [mem])] at h
    by_cases h1 : mem t' [] = true
    · obtain ⟨lf', rfl⟩ := eq_leaf_of_mem_nil h1
      have h2 : mem t'' [] = false := by
        by_cases h2 : mem t'' [] = true
        · exact absurd (h1.trans h2.symm) hnil
        · simpa using h2
      have hz : ∀ et, mem t'' et = false := by
        intro et
        match et with
        | [] => exact h2
        | e :: et => exact (hcons e et).2
      rw [size_leaf, size_eq_zero_of_not_mem hz, size_leaf]
    · have h1' : mem t' [] = false := by simpa using h1
      have h2 : mem t'' [] = true := by
        by_cases h2 : mem t'' [] = true
        · exact h2
        · have h2' : mem t'' [] = false := by simpa using h2
          exact absurd (h1'.trans h2'.symm) hnil
      obtain ⟨lf'', rfl⟩ := eq_leaf_of_mem_nil h2
      have hz : ∀ et, mem t' et = false := by
        intro et
        match et with
        | [] => exact h1'
        | e :: et => exact (hcons e et).1
      rw [size_leaf, size_eq_zero_of_not_mem hz, size_leaf]
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro t' t'' hp
    have hnil := hp []
    rw [ite_eq_right (by simp [mem])] at hnil
    have hz : ∀ (u : Ctree), mem u [] = false → ∀ lf : Ctree, u ≠ .leaf lf := by
      intro u hu lf hlf
      rw [hlf] at hu
      simp [mem, sub] at hu
    cases t' with
    | leaf lf' => exact absurd rfl (hz _ hnil.1 lf')
    | empty =>
      cases t'' with
      | leaf lf'' => exact absurd rfl (hz _ hnil.2 lf'')
      | empty =>
        have hnone : ∀ et, mem (Ctree.node t₁ t₂ t₃) et = false := by
          intro et
          have h := hp et
          by_cases hm : mem (Ctree.node t₁ t₂ t₃) et = true
          · rw [ite_eq_left hm] at h
            simp at h
          · simpa using hm
        rw [size_eq_zero_of_not_mem hnone, size_empty]
      | node b₁ b₂ b₃ =>
        have p₁ : PairPartition t₁ (.empty, b₁) := fun et => hp (Color.c1 :: et)
        have p₂ : PairPartition t₂ (.empty, b₂) := fun et => hp (Color.c2 :: et)
        have p₃ : PairPartition t₃ (.empty, b₃) := fun et => hp (Color.c3 :: et)
        rw [size_node, size_node, size_empty, ih₁ p₁, ih₂ p₂, ih₃ p₃]
        simp
    | node a₁ a₂ a₃ =>
      cases t'' with
      | leaf lf'' => exact absurd rfl (hz _ hnil.2 lf'')
      | empty =>
        have p₁ : PairPartition t₁ (a₁, .empty) := fun et => hp (Color.c1 :: et)
        have p₂ : PairPartition t₂ (a₂, .empty) := fun et => hp (Color.c2 :: et)
        have p₃ : PairPartition t₃ (a₃, .empty) := fun et => hp (Color.c3 :: et)
        rw [size_node, size_node, size_empty, ih₁ p₁, ih₂ p₂, ih₃ p₃]
        simp
      | node b₁ b₂ b₃ =>
        have p₁ : PairPartition t₁ (a₁, b₁) := fun et => hp (Color.c1 :: et)
        have p₂ : PairPartition t₂ (a₂, b₂) := fun et => hp (Color.c2 :: et)
        have p₃ : PairPartition t₃ (a₃, b₃) := fun et => hp (Color.c3 :: et)
        rw [size_node, size_node, size_node, ih₁ p₁, ih₂ p₂, ih₃ p₃]
        omega

/-- A proper tree of height `h` holds at most `3 ^ h` traces. -/
theorem size_le : ∀ {h : ℕ} {t : Ctree}, Proper h t → size t ≤ 3 ^ h
  | 0, .leaf _, _ => by simp
  | 0, .empty, _ => by simp
  | h + 1, .node t₁ t₂ t₃, hp => by
    obtain ⟨-, h₁, h₂, h₃⟩ := hp
    have := size_le h₁
    have := size_le h₂
    have := size_le h₃
    rw [size_node, pow_succ]
    omega
  | h + 1, .empty, _ => by simp

end Ctree

/-! ### The closure loop -/

/-- One improvement step: restrict the colouring tree by the chromograms that
have been deleted, then close up again with the rotations of what that
removed. -/
def kempeStep (h : ℕ)
    (closure : Ctree → Ctree → Gtree → Ctree × Gtree × Gtree)
    (kr : Ctree × Gtree × Gtree) : Ctree × Gtree × Gtree :=
  let (ctu, gtr, gtu) := kr
  if ctu.isEmpty then kr
  else if gtr.isEmpty then kr
  else if gtu.isEmpty then (.empty, .empty, .empty)
  else
    let (ctu', ctr) := Ctree.restrict h ctu (ctrCons [] gtr [])
    closure ctu' ctr.rotlr gtu

/-- Two improvement steps after a closure call. -/
def kempeStep2c (h : ℕ) (closure : Ctree → Ctree → Gtree → Ctree × Gtree × Gtree)
    (ctu ctr : Ctree) (gtu : Gtree) : Ctree × Gtree × Gtree :=
  kempeStep h closure (kempeStep h closure (closure ctu ctr gtu))

/-- The Kempe closure loop: `d` rounds of two improvement steps, which perform
up to `3 ^ d` restriction cycles and so converge. -/
def kempeTreeClosure (h : ℕ) : ℕ → Ctree → Ctree → Gtree → Ctree × Gtree × Gtree
  | 0, ctu, ctr, gtu =>
      let (gtr, gtu') := gtreeRestrict gtu (gtrCons [] ctr [])
      (ctu, gtr, gtu')
  | d + 1, ctu, ctr, gtu => kempeStep2c h (kempeTreeClosure h d) ctu ctr gtu

/-! ### The loop invariant

A state of the loop is valid when the colouring tree holds exactly the even
traces the two gram trees still match, everything the restriction tree holds is
in the Kempe co-closure, and every well-formed chromogram that has been deleted
matched such a trace.
-/

/-- A valid intermediate state of the Kempe closure loop. -/
structure KempeValid (h : ℕ) (P : List Color → Prop) (ctu ctr : Ctree)
    (gtr gtu : Gtree) : Prop where
  /-- The colouring tree is proper. -/
  proper : Ctree.Proper (h + 1) ctu
  /-- It holds exactly the even traces the two gram trees match. -/
  sub : ∀ et, Ctree.sub ctu et =
    if evenTrace et then Gtree.sub gtr [] et + Gtree.sub gtu [] et else 0
  /-- The restriction tree holds only traces of the Kempe co-closure. -/
  restricted : ∀ et, Ctree.mem ctr et →
    KempeCoclosure P (completeTrace et) ∧ et.length = h + 1
  /-- The deleted chromograms are no longer available, and are well formed. -/
  deleted : ∀ w, Gtree.mem gtr w → ¬ Gtree.mem gtu w ∧ initGtreeSpec (h + 1) w
  /-- The available chromograms are well formed. -/
  available : ∀ w, Gtree.mem gtu w → initGtreeSpec (h + 1) w
  /-- Every well-formed chromogram that is no longer available matched a trace
  of the Kempe co-closure. -/
  closed : ∀ w, ¬ Gtree.mem gtu w → initGtreeSpec (h + 1) w →
    ∃ et, KempeCoclosure P (completeTrace et) ∧ matchpg [] et w

/-- The loop has made progress, and accounts for every trace it has dropped. -/
structure KempeComplete (P : List Color → Prop) (sz : ℕ) (ctu ctr : Ctree)
    (gtr gtu : Gtree) : Prop where
  /-- Either the colouring tree has shrunk, or the restriction is exhausted. -/
  progress : Ctree.size ctu < sz ∨ (ctr = .empty ∧ ∀ w, ¬ Gtree.mem gtr w)
  /-- A trace the predicate holds, or that the colouring tree has lost in some
  rotation, is either in the restriction tree or matched by nothing. -/
  accounted : ∀ et,
    (P (completeTrace et) ∨ ∃ e : Color, ¬ Ctree.mem ctu ((evenize et).map (EdgePerm.edgeRot e)))
      → Ctree.mem ctr (evenize et) ∨ Gtree.sub gtu [] et = 0

/-! ### Correctness of the closure loop -/

namespace Ctree

/-- A proper tree of size zero is empty. -/
theorem size_eq_zero : ∀ {h : ℕ} {t : Ctree}, Proper h t → size t = 0 → t = .empty
  | 0, .empty, _, _ => rfl
  | 0, .leaf _, _, hsz => by simp at hsz
  | 0, .node _ _ _, hp, _ => absurd hp not_false
  | _ + 1, .empty, _, _ => rfl
  | _ + 1, .leaf _, hp, _ => absurd hp not_false
  | _ + 1, .node t₁ t₂ t₃, hp, hsz => by
    obtain ⟨hne, h₁, h₂, h₃⟩ := hp
    rw [size_node] at hsz
    rw [size_eq_zero h₁ (by omega), size_eq_zero h₂ (by omega),
      size_eq_zero h₃ (by omega)] at hne
    simp [isEmptyNode] at hne

/-- Membership is nonzero multiplicity. -/
theorem mem_iff_sub_ne_zero (t : Ctree) (et : List Color) :
    mem t et = true ↔ sub t et ≠ 0 := by simp [mem]

/-- Reading a colouring tree partition at one trace. -/
theorem mem_of_pairPartition {t : Ctree} {p : Ctree × Ctree} (hp : PairPartition t p)
    (et : List Color) :
    mem t et = (mem p.1 et || mem p.2 et) ∧ (mem p.1 et && mem p.2 et) = false := by
  have h := hp et
  cases h1 : mem p.1 et <;> cases h2 : mem p.2 et <;> cases ht : mem t et <;> simp_all

end Ctree

/-- Reading a chromogram tree partition at one chromogram. -/
theorem mem_of_pairPartition {t : Gtree} {p : Gtree × Gtree} (hp : PairPartition t p)
    (w : Chromogram) :
    Gtree.mem t w = (Gtree.mem p.1 w || Gtree.mem p.2 w) ∧
      (Gtree.mem p.1 w && Gtree.mem p.2 w) = false := by
  have h := hp w
  cases h1 : Gtree.mem p.1 w <;> cases h2 : Gtree.mem p.2 w <;>
    cases ht : Gtree.mem t w <;> simp_all

/-! #### Unfolding the loop -/

/-- One improvement step, on an explicit state. -/
theorem kempeStep_eq (h : ℕ)
    (closure : Ctree → Ctree → Gtree → Ctree × Gtree × Gtree) (ctu : Ctree)
    (gtr gtu : Gtree) :
    kempeStep h closure (ctu, gtr, gtu) =
      if ctu.isEmpty then (ctu, gtr, gtu)
      else if gtr.isEmpty then (ctu, gtr, gtu)
      else if gtu.isEmpty then (.empty, .empty, .empty)
      else closure (Ctree.restrict h ctu (ctrCons [] gtr [])).1
        (Ctree.restrict h ctu (ctrCons [] gtr [])).2.rotlr gtu := rfl

/-- The loop with no rounds left just restricts the gram tree. -/
@[simp] theorem kempeTreeClosure_zero (h : ℕ) (ctu ctr : Ctree) (gtu : Gtree) :
    kempeTreeClosure h 0 ctu ctr gtu = (ctu, gtreeRestrict gtu (gtrCons [] ctr [])) := rfl

/-- The loop with `d + 1` rounds left runs one closure and two steps. -/
theorem kempeTreeClosure_succ (h d : ℕ) (ctu ctr : Ctree) (gtu : Gtree) :
    kempeTreeClosure h (d + 1) ctu ctr gtu =
      kempeStep h (kempeTreeClosure h d)
        (kempeStep h (kempeTreeClosure h d) (kempeTreeClosure h d ctu ctr gtu)) := rfl

/-! #### The correctness statement -/

/-- A state returned by the loop is valid: its restriction tree is exhausted. -/
def KtrValid (h : ℕ) (P : List Color → Prop) (kr : Ctree × Gtree × Gtree) : Prop :=
  KempeValid h P kr.1 .empty kr.2.1 kr.2.2

/-- A state returned by the loop has made progress up to `sz`. -/
def KtrComplete (P : List Color → Prop) (sz : ℕ) (kr : Ctree × Gtree × Gtree) : Prop :=
  KempeComplete P sz kr.1 .empty kr.2.1 kr.2.2

/-- An approximation of the closure loop is correct when it turns a valid state
into a valid returned state, and improves the progress bound from `3 ^ d + sz`
to `sz + 1`. -/
def KtcCorrect (h d : ℕ) (P : List Color → Prop)
    (closure : Ctree → Ctree → Gtree → Ctree × Gtree × Gtree) : Prop :=
  ∀ ctu ctr gtu, KempeValid h P ctu ctr .empty gtu →
    KtrValid h P (closure ctu ctr gtu) ∧
      ∀ sz, KempeComplete P (3 ^ d + sz) ctu ctr .empty gtu →
        KtrComplete P (sz + 1) (closure ctu ctr gtu)

/-! #### The base case -/

/-- The simplest approximation — restrict the gram tree by the restriction tree —
is already correct for `d = 0`. -/
theorem ktcCorrect_zero (h : ℕ) (P : List Color → Prop) :
    KtcCorrect h 0 P (kempeTreeClosure h 0) := by
  intro ctu ctr gtu hv
  have hprop := hv.proper
  have hsub := hv.sub
  have hrestr := hv.restricted
  have havail := hv.available
  have hclosed := hv.closed
  set r : GtreeRestriction := gtrCons [] ctr [] with hrdef
  set gr := gtreeRestrict gtu r with hgrdef
  have hpart : PairPartition gtu gr := gtreeRestrict_partition gtu r
  have hfst : ∀ w, Gtree.mem gr.1 w = (Gtree.mem gtu w && gtrMem r w) :=
    fun w => mem_fst_gtreeRestrict gtu r w
  have hrmem : ∀ w, gtrMem r w = hasMatch [] (Ctree.mem ctr) w := by
    intro w; rw [hrdef, gtrMem_gtrCons, gtrMem_nil, Bool.or_false]
  have hsplit : ∀ et, Gtree.sub gtu [] et = Gtree.sub gr.1 [] et + Gtree.sub gr.2 [] et :=
    fun et => matchCount_partition et (Gtree.mem gtu) (Gtree.mem gr.1) (Gtree.mem gr.2) []
      hpart
  have hvalid : KempeValid h P ctu .empty gr.1 gr.2 := by
    refine ⟨hprop, ?_, ?_, ?_, ?_, ?_⟩
    · intro et
      rw [hsub et, Gtree.sub_empty, Nat.zero_add, hsplit et]
    · intro et hm; simp at hm
    · intro w hw
      obtain ⟨hor, hand⟩ := mem_of_pairPartition hpart w
      have hgu : Gtree.mem gtu w = true := by
        have := hfst w
        rw [hw] at this
        cases hc : Gtree.mem gtu w
        · rw [hc] at this; simp at this
        · rfl
      refine ⟨?_, havail w hgu⟩
      rw [hw] at hand
      simp at hand
      simp [hand]
    · intro w hw
      obtain ⟨hor, -⟩ := mem_of_pairPartition hpart w
      exact havail w (by rw [hor, hw]; simp)
    · intro w hw hspec
      by_cases hgu : Gtree.mem gtu w = true
      · have h1 : Gtree.mem gr.1 w = true := by
          obtain ⟨hor, -⟩ := mem_of_pairPartition hpart w
          rw [hor] at hgu
          cases hc : Gtree.mem gr.1 w
          · rw [hc, Bool.false_or] at hgu; exact absurd hgu hw
          · rfl
        rw [hfst w, hgu, Bool.true_and, hrmem w] at h1
        obtain ⟨et, hct, hm⟩ := (hasMatch_iff w [] (Ctree.mem ctr)).mp h1
        exact ⟨et, (hrestr et hct).1, hm⟩
      · exact hclosed w (by simpa using hgu) hspec
  refine ⟨hvalid, ?_⟩
  intro sz hc
  have hprog := hc.progress
  have hacc := hc.accounted
  have hgoal : KempeComplete P (sz + 1) ctu .empty gr.1 gr.2 := by
    refine ⟨?_, ?_⟩
    · rcases hprog with hlt | ⟨hctr0, -⟩
      · left; simp only [pow_zero] at hlt; omega
      · right
        refine ⟨rfl, ?_⟩
        intro w hw
        rw [hfst w, hrmem w, hctr0,
          hasMatch_eq_false (fun et => Ctree.mem_empty et)] at hw
        simp at hw
    · intro et hp
      right
      by_contra hne
      obtain ⟨w, hgw, hmw⟩ := (matchCount_ne_zero_iff et (Gtree.mem gr.2) []).mp hne
      obtain ⟨hor, hand⟩ := mem_of_pairPartition hpart w
      have hgu : Gtree.mem gtu w = true := by rw [hor, hgw]; simp
      have hg1 : Gtree.mem gr.1 w = false := by rw [hgw] at hand; simpa using hand
      rcases hacc et hp with hmem | hz
      · rw [hfst w, hgu, Bool.true_and, hrmem w] at hg1
        have hmt : hasMatch [] (Ctree.mem ctr) w = true :=
          (hasMatch_iff w [] (Ctree.mem ctr)).mpr
            ⟨evenize et, hmem, by rw [matchpg_evenize]; exact hmw⟩
        rw [hmt] at hg1; simp at hg1
      · exact absurd hz ((matchCount_ne_zero_iff et (Gtree.mem gtu) []).mpr ⟨w, hgu, hmw⟩)
  exact hgoal

/-! #### The single improvement step -/

/-- The reference's `IHstep`: one improvement step, applied to a valid returned
state, gives another valid returned state, and improves the progress bound from
`3 ^ d + (sz + 1)` to `sz + 1`. -/
theorem kempeStep_correct {h d : ℕ} {P : List Color → Prop}
    {closure : Ctree → Ctree → Gtree → Ctree × Gtree × Gtree}
    (hcl : KtcCorrect h d P closure) (kr : Ctree × Gtree × Gtree) (hv : KtrValid h P kr) :
    KtrValid h P (kempeStep h closure kr) ∧
      ∀ sz, KtrComplete P (3 ^ d + (sz + 1)) kr →
        KtrComplete P (sz + 1) (kempeStep h closure kr) := by
  obtain ⟨ctu, gtr, gtu⟩ := kr
  have hv' : KempeValid h P ctu .empty gtr gtu := hv
  have hprop := hv'.proper
  have hsub := hv'.sub
  have hdel := hv'.deleted
  have havail := hv'.available
  have hclosed := hv'.closed
  rw [kempeStep_eq]
  by_cases hcu : ctu.isEmpty = true
  · rw [ite_eq_left hcu]
    refine ⟨hv, ?_⟩
    intro sz hc
    exact ⟨Or.inl (by rw [Ctree.eq_empty_of_isEmpty hcu]; simp), hc.accounted⟩
  by_cases hgr : gtr.isEmpty = true
  · rw [ite_eq_right hcu, ite_eq_left hgr]
    refine ⟨hv, ?_⟩
    intro sz hc
    refine ⟨Or.inr ⟨rfl, ?_⟩, hc.accounted⟩
    intro w hw
    rw [Gtree.isEmpty_eq_true.mp hgr] at hw
    simp at hw
  by_cases hgu : gtu.isEmpty = true
  · rw [ite_eq_right hcu, ite_eq_right hgr, ite_eq_left hgu]
    have hgu' : gtu = .empty := Gtree.isEmpty_eq_true.mp hgu
    have hval : KempeValid h P .empty .empty .empty .empty := by
      refine ⟨trivial, fun et => by simp, fun et hm => by simp at hm,
        fun w hw => by simp at hw, fun w hw => by simp at hw, ?_⟩
      intro w hw hspec
      exact hclosed w (by rw [hgu']; simp) hspec
    refine ⟨hval, ?_⟩
    intro sz _
    exact ⟨Or.inl (by simp), fun et _ => Or.inr (by simp)⟩
  rw [ite_eq_right hcu, ite_eq_right hgr, ite_eq_right hgu]
  set r : CtreeRestriction := ctrCons [] gtr [] with hrdef
  set cp := Ctree.restrict h ctu r with hcpdef
  obtain ⟨hcu1, hcr1, hpart, hdsub⟩ := Ctree.restrict_correct h ctu r hprop
  rw [← hcpdef] at hcu1 hcr1 hpart hdsub
  have hkey : ∀ (b : Bool) (A B : ℕ),
      (if b = true then A + B else 0) - A = if b = true then B else 0 := by
    intro b A B; cases b <;> simp
  have hDctu' : ∀ et, Ctree.sub cp.1 et = if evenTrace et then Gtree.sub gtu [] et else 0 := by
    intro et
    rw [hdsub et, hsub et, hrdef, ctrSub_ctrCons, ctrSub_nil, Nat.add_zero]
    exact hkey _ _ _
  -- The state after the restriction is valid.
  have gtValid : KempeValid h P cp.1 (Ctree.rotlr cp.2) .empty gtu := by
    refine ⟨hcu1, fun et => by rw [hDctu' et, Gtree.sub_empty, Nat.zero_add], ?_,
      fun w hw => by simp at hw, havail, hclosed⟩
    intro et0 hmem0
    rw [Ctree.mem_rotlr et0 hcr1, Bool.or_eq_true] at hmem0
    obtain ⟨g, hct⟩ : ∃ g : EdgePerm, Ctree.mem cp.2 (et0.map g) = true := by
      rcases hmem0 with hm | hm
      · exact ⟨EdgePerm.e312, hm⟩
      · exact ⟨EdgePerm.e231, hm⟩
    set et := et0.map g with hetdef
    obtain ⟨hor, hand⟩ := Ctree.mem_of_pairPartition hpart et
    have hmu : Ctree.mem ctu et = true := by rw [hor, hct]; simp
    have hmu' : Ctree.mem cp.1 et = false := by rw [hct] at hand; simpa using hand
    have heven : evenTrace et = true := by
      by_contra hne
      have hz : Ctree.sub ctu et = 0 := by rw [hsub et, ite_eq_right hne]
      exact ((Ctree.mem_iff_sub_ne_zero _ _).mp hmu) hz
    have hgu0 : Gtree.sub gtu [] et = 0 := by
      have h1 := hDctu' et
      rw [ite_eq_left heven] at h1
      have h0 : Ctree.sub cp.1 et = 0 := by
        by_contra hz
        rw [(Ctree.mem_iff_sub_ne_zero _ _).mpr hz] at hmu'
        simp at hmu'
      omega
    have hgr0 : Gtree.sub gtr [] et ≠ 0 := by
      have h1 := hsub et
      rw [ite_eq_left heven, hgu0, Nat.add_zero] at h1
      rw [← h1]
      exact (Ctree.mem_iff_sub_ne_zero _ _).mp hmu
    have hlen : et.length = h + 1 := by
      obtain ⟨w, hgw, hmw⟩ := (matchCount_ne_zero_iff et (Gtree.mem gtr) []).mp hgr0
      have hspec := (hdel w hgw).2
      rw [initGtreeSpec, gspec, Bool.and_eq_true, beq_iff_eq] at hspec
      rw [← matchpg_length et [] w hmw]
      exact hspec.1
    refine ⟨?_, by rw [hetdef, List.length_map] at hlen; exact hlen⟩
    intro P1 hP1closed hP1et0
    have hP1et : P1 (completeTrace et) := by
      rw [hetdef, map_completeTrace]
      exact (hP1closed _ hP1et0).1 g
    obtain ⟨-, w, hetMw, hwP1⟩ := hP1closed _ hP1et
    have hbal : balanced 0 false w := by
      have hb := (matchg_balanced hetMw).2
      rwa [sum_completeTrace, Color.lo_zero] at hb
    set w1 := w.take (w.length - 1) with hw1def
    have hDw : w = cgram 0 false w1 := matchg_cgram hetMw
    have hbal1 : balanced 0 false (cgram 0 false w1) := by rw [← hDw]; exact hbal
    have hetMw1 : matchpg [] et w1 = true := by
      rw [← matchg_completeTrace et w1 hbal1, ← hDw]
      exact hetMw
    have hnotgtu : Gtree.mem gtu w1 = false := by
      cases hc : Gtree.mem gtu w1
      · rfl
      · exact absurd hgu0
          ((matchCount_ne_zero_iff et (Gtree.mem gtu) []).mpr ⟨w1, hc, hetMw1⟩)
    have hspec1 : initGtreeSpec (h + 1) w1 = true := by
      rw [initGtreeSpec, gspec, Bool.and_eq_true, beq_iff_eq]
      exact ⟨by rw [matchpg_length et [] w1 hetMw1, hlen], hbal1⟩
    obtain ⟨et1, hcoclos1, het1Mw1⟩ := hclosed w1 (by rw [hnotgtu]; simp) hspec1
    refine hcoclos1 P1 hP1closed (hwP1 _ ?_)
    rw [hDw, matchg_completeTrace et1 w1 hbal1]
    exact het1Mw1
  -- The state after the restriction has made progress.
  have gtFull : ∀ sz, KempeComplete P (sz + 1) ctu .empty gtr gtu →
      KempeComplete P sz cp.1 (Ctree.rotlr cp.2) .empty gtu := by
    intro sz hc
    have hprog := hc.progress
    have hacc := hc.accounted
    have hszpart : Ctree.size ctu = Ctree.size cp.1 + Ctree.size cp.2 :=
      Ctree.size_of_pairPartition hpart
    refine ⟨?_, ?_⟩
    · rcases hprog with hlt | ⟨-, hgr0⟩
      · rcases Nat.eq_zero_or_pos (Ctree.size cp.2) with h0 | h0
        · right
          refine ⟨by rw [Ctree.size_eq_zero hcr1 h0]; rfl, fun w hw => by simp at hw⟩
        · left; omega
      · right
        refine ⟨?_, fun w hw => by simp at hw⟩
        have hgrz : ∀ et, Gtree.sub gtr [] et = 0 := fun et =>
          matchCount_eq_zero et (Gtree.mem gtr) [] fun w => by simpa using hgr0 w
        have hsame : ∀ et, Ctree.sub cp.1 et = Ctree.sub ctu et := by
          intro et
          rw [hDctu' et, hsub et, hgrz et, Nat.zero_add]
        have hpart2 : Ctree.PairPartition ctu (cp.1, .empty) := by
          intro et
          have h1 : Ctree.mem cp.1 et = Ctree.mem ctu et := by
            simp only [Ctree.mem, hsame et]
          cases hm : Ctree.mem ctu et <;> simp_all
        have hsz2 : Ctree.size ctu = Ctree.size cp.1 + Ctree.size .empty :=
          Ctree.size_of_pairPartition hpart2
        rw [Ctree.size_empty] at hsz2
        rw [Ctree.size_eq_zero hcr1 (by omega)]
        rfl
    · intro et hp
      rcases hp with hPet | ⟨e, hne⟩
      · rcases hacc et (Or.inl hPet) with hm | hz
        · exact absurd hm (by simp)
        · exact Or.inr hz
      by_cases hcu'e : Ctree.mem cp.1 (evenize et) = true
      · by_cases hcue1 : Ctree.mem ctu ((evenize et).map (EdgePerm.edgeRot e)) = true
        · left
          obtain ⟨-, hand1⟩ := Ctree.mem_of_pairPartition hpart (evenize et)
          have h2e : Ctree.mem cp.2 (evenize et) = false := by
            rw [hcu'e] at hand1; simpa using hand1
          obtain ⟨hor2, -⟩ :=
            Ctree.mem_of_pairPartition hpart ((evenize et).map (EdgePerm.edgeRot e))
          have h2e1 : Ctree.mem cp.2 ((evenize et).map (EdgePerm.edgeRot e)) = true := by
            rw [hor2] at hcue1
            have h1 : Ctree.mem cp.1 ((evenize et).map (EdgePerm.edgeRot e)) = false := by
              simpa using hne
            rw [h1, Bool.false_or] at hcue1
            exact hcue1
          rw [Ctree.mem_rotlr (evenize et) hcr1, Bool.or_eq_true]
          cases e with
          | c0 =>
            rw [show EdgePerm.edgeRot Color.c0 = 1 from rfl, map_one_edgePerm, h2e] at h2e1
            simp at h2e1
          | c1 =>
            rw [show EdgePerm.edgeRot Color.c1 = 1 from rfl, map_one_edgePerm, h2e] at h2e1
            simp at h2e1
          | c2 => exact Or.inl h2e1
          | c3 => exact Or.inr h2e1
        · rcases hacc et (Or.inr ⟨e, by simpa using hcue1⟩) with hm | hz
          · exact absurd hm (by simp)
          · exact Or.inr hz
      · right
        by_contra hzne
        obtain ⟨w, hgw, hmw⟩ := (matchCount_ne_zero_iff et (Gtree.mem gtu) []).mp hzne
        refine hcu'e ?_
        rw [Ctree.mem_iff_sub_ne_zero, hDctu' (evenize et), ite_eq_left (evenTrace_evenize et)]
        exact (matchCount_ne_zero_iff (evenize et) (Gtree.mem gtu) []).mpr
          ⟨w, hgw, by rw [matchpg_evenize]; exact hmw⟩
  obtain ⟨hclv, hclf⟩ := hcl cp.1 (Ctree.rotlr cp.2) gtu gtValid
  refine ⟨hclv, ?_⟩
  intro sz hc
  have hc' : KempeComplete P (3 ^ d + sz + 1) ctu .empty gtr gtu := by
    have : KempeComplete P (3 ^ d + (sz + 1)) ctu .empty gtr gtu := hc
    rwa [← Nat.add_assoc] at this
  exact hclf sz (gtFull (3 ^ d + sz) hc')

/-! #### The loop -/

/-- The reference's `Kempe_tree_closure_correct`: `d` rounds of the loop turn a
valid state into a valid returned state, and improve the progress bound from
`3 ^ d + sz` to `sz + 1`. -/
theorem kempeTreeClosure_correct (h : ℕ) (P : List Color → Prop) :
    ∀ d, KtcCorrect h d P (kempeTreeClosure h d)
  | 0 => ktcCorrect_zero h P
  | d + 1 => by
    intro ctu ctr gtu hv
    obtain ⟨hv1, hf1⟩ := kempeTreeClosure_correct h P d ctu ctr gtu hv
    obtain ⟨hv2, hf2⟩ :=
      kempeStep_correct (kempeTreeClosure_correct h P d) _ hv1
    obtain ⟨hv3, hf3⟩ :=
      kempeStep_correct (kempeTreeClosure_correct h P d) _ hv2
    refine ⟨hv3, ?_⟩
    intro sz hcomp
    have e1 : 3 ^ (d + 1) + sz = 3 ^ d + (3 ^ d + (3 ^ d + sz)) := by
      rw [pow_succ]; omega
    rw [e1] at hcomp
    have s1 := hf1 (3 ^ d + (3 ^ d + sz)) hcomp
    rw [show 3 ^ d + (3 ^ d + sz) + 1 = 3 ^ d + (3 ^ d + sz + 1) by omega] at s1
    have s2 := hf2 (3 ^ d + sz) s1
    rw [show 3 ^ d + sz + 1 = 3 ^ d + (sz + 1) by omega] at s2
    exact hf3 sz s2

/-! ### Auxiliary facts about traces

Two small facts used to set up and read off the loop: rotating a trace does not
change its parity, and a trace summing to zero has an even number of colours
with the high bit set, hence a positive Dyck multiplicity.
-/

/-- The number of high-bit colours in a list has the parity of the high bit of
its sum. -/
theorem countHi_mod_two (l : List Color) : countHi l % 2 = if l.sum.hi then 1 else 0 := by
  induction l with
  | nil => simp [countHi]
  | cons c l ih =>
    rw [countHi, List.countP_cons, ← countHi, List.sum_cons, Color.hi_add]
    cases hc : c.hi <;> cases hs : l.sum.hi <;> simp_all <;> omega

/-- A trace summing to zero has a positive Dyck multiplicity. -/
theorem dyck_countHi_pos {l : List Color} (h : l.sum = 0) : 0 < dyck (countHi l) := by
  have hm := countHi_mod_two l
  rw [h, Color.hi_zero] at hm
  have hm2 : countHi l % 2 = 0 := by simpa using hm
  obtain ⟨n, hn⟩ : ∃ n, countHi l = 2 * n := ⟨countHi l / 2, by omega⟩
  rw [hn]
  exact dyck_two_mul_pos n

/-- The rotations of the three colours preserve the normalised tail of a trace. -/
theorem normTail_map_rot {g : EdgePerm}
    (hg : g = 1 ∨ g = EdgePerm.e312 ∨ g = EdgePerm.e231) (u : List Color) :
    normTail (u.map g) = normTail u := by
  cases u with
  | nil => simp [normTail]
  | cons c t =>
    by_cases hc : c = 0
    · subst hc
      simp [normTail]
    · have hgc : ¬ g c = 0 := by simpa using hc
      have hrot : EdgePerm.rotTo (g c) * g = EdgePerm.rotTo c := by
        revert hc; rcases hg with rfl | rfl | rfl <;> cases c <;> decide
      simp only [List.map_cons, normTail, ite_eq_right hgc, ite_eq_right hc,
        map_map_edgePerm, hrot]

/-- The rotations of the three colours preserve the parity of a trace. -/
theorem evenTrace_map_rot {g : EdgePerm}
    (hg : g = 1 ∨ g = EdgePerm.e312 ∨ g = EdgePerm.e231) (u : List Color) :
    evenTrace (u.map g) = evenTrace u := by
  rw [evenTrace, evenTrace, normTail_map_rot hg]

/-- Every colour rotation is a rotation of the three colours. -/
theorem edgeRot_eq_rot (e : Color) :
    EdgePerm.edgeRot e = 1 ∨ EdgePerm.edgeRot e = EdgePerm.e312 ∨
      EdgePerm.edgeRot e = EdgePerm.e231 := by
  cases e <;> simp [EdgePerm.edgeRot]

/-- Match counts of a gram tree are match counts of its membership test. -/
theorem Gtree.sub_eq_matchCount (t : Gtree) (bs : List Bool) (et : List Color) :
    Gtree.sub t bs et = matchCount (Gtree.mem t) bs et := rfl

/-! ### Setting up and reading off the loop -/

/-- The reference's `Kempe_valid_restrict`: adding a restriction tree whose
traces satisfy `P` keeps a state valid. -/
theorem kempeValid_restrict {h : ℕ} {P : List Color → Prop} {ctu ctr : Ctree}
    {gtr gtu : Gtree} (hctr : ∀ et, Ctree.mem ctr et → P (completeTrace et) ∧ et.length = h + 1)
    (hv : KempeValid h P ctu .empty gtr gtu) : KempeValid h P ctu ctr gtr gtu :=
  ⟨hv.proper, hv.sub,
    fun et hm => ⟨fun _ _ hP1 => ⟨completeTrace et, (hctr et hm).1, hP1⟩, (hctr et hm).2⟩,
    hv.deleted, hv.available, hv.closed⟩

/-- The reference's `Kempe_valid_init`: the initial colouring and gram trees are
a valid starting state. -/
theorem kempeValid_init (h : ℕ) (P : List Color → Prop) :
    KempeValid h P (initTree (h + 1)) .empty .empty (gtreeInitTree (h + 1)) := by
  have hgsub : ∀ et, Gtree.sub (gtreeInitTree (h + 1)) [] et =
      if et.length = h + 1 ∧ (0 : Color) ∉ completeTrace et
      then dyck (countHi (completeTrace et)) else 0 := by
    intro et
    rw [Gtree.sub_eq_matchCount,
      matchCount_congr et _ (initGtreeSpec (h + 1)) [] (mem_gtreeInitTree (h + 1)),
      matchCount_initGtreeSpec]
  refine ⟨initTree_proper (h + 1), ?_, fun et hm => by simp at hm,
    fun w hw => by simp at hw, ?_, ?_⟩
  · intro et
    rw [sub_initTree, Gtree.sub_empty, Nat.zero_add, hgsub et]
    by_cases he : evenTrace et = true
    · rw [ite_eq_left he]
      by_cases hd : et.length = h + 1 ∧ (0 : Color) ∉ completeTrace et
      · rw [ite_eq_left hd, ite_eq_left ⟨hd.1, hd.2, he⟩]
      · rw [ite_eq_right hd, ite_eq_right (fun hc => hd ⟨hc.1, hc.2.1⟩)]
    · rw [ite_eq_right he, ite_eq_right (fun hc => he hc.2.2)]
  · intro w hw
    rwa [mem_gtreeInitTree] at hw
  · intro w hw hspec
    exact absurd (by rwa [mem_gtreeInitTree]) hw

/-- The reference's `Kempe_validP`: a trace the colouring tree has dropped is in
the Kempe co-closure. -/
theorem kempeCoclosure_of_not_mem {h : ℕ} {P : List Color → Prop} {ctu ctr : Ctree}
    {gtr gtu : Gtree} (hv : KempeValid h P ctu ctr gtr gtu) {et0 : List Color}
    (hlen : et0.length = h + 1) (hmem : Ctree.mem ctu (evenize et0) = false) :
    KempeCoclosure P (completeTrace et0) := by
  intro P1 hP1closed hP1et0
  have hP1et : P1 (completeTrace (evenize et0)) := by
    rw [evenize, map_completeTrace]
    exact (hP1closed _ hP1et0).1 _
  obtain ⟨-, w0, hMw0, hw0P1⟩ := hP1closed _ hP1et
  have hbal0 : balanced 0 false w0 := by
    have hb := (matchg_balanced hMw0).2
    rwa [sum_completeTrace, Color.lo_zero] at hb
  set w := w0.take (w0.length - 1) with hwdef
  have hDw : w0 = cgram 0 false w := matchg_cgram hMw0
  have hbal : balanced 0 false (cgram 0 false w) := by rw [← hDw]; exact hbal0
  have hMw : matchpg [] (evenize et0) w = true := by
    rw [← matchg_completeTrace (evenize et0) w hbal, ← hDw]; exact hMw0
  have hnotgtu : Gtree.mem gtu w = false := by
    cases hc : Gtree.mem gtu w
    · rfl
    · exfalso
      have hne : Gtree.sub gtu [] (evenize et0) ≠ 0 :=
        (matchCount_ne_zero_iff _ _ []).mpr ⟨w, hc, hMw⟩
      have hs := hv.sub (evenize et0)
      rw [ite_eq_left (evenTrace_evenize et0)] at hs
      have hsne : Ctree.sub ctu (evenize et0) ≠ 0 := by omega
      rw [(Ctree.mem_iff_sub_ne_zero _ _).mpr hsne] at hmem
      simp at hmem
  have hspec : initGtreeSpec (h + 1) w = true := by
    rw [initGtreeSpec, gspec, Bool.and_eq_true, beq_iff_eq]
    refine ⟨?_, hbal⟩
    rw [matchpg_length _ [] w hMw, evenize, List.length_map, hlen]
  obtain ⟨et1, hco1, hM1⟩ := hv.closed w (by rw [hnotgtu]; simp) hspec
  refine hco1 P1 hP1closed (hw0P1 _ ?_)
  rw [hDw, matchg_completeTrace et1 w hbal]
  exact hM1

/-- The reference's `Kempe_complete_init`: the initial state has made no
progress yet, but accounts for every trace, provided the restriction tree holds
every even trace the predicate admits. -/
theorem kempeComplete_init {h : ℕ} {P : List Color → Prop} {ctr : Ctree}
    (hPctr : ∀ et, P (completeTrace et) → Ctree.mem ctr (evenize et)) (gtr : Gtree) :
    KempeComplete P (3 ^ (h + 2)) (initTree (h + 1)) ctr gtr (gtreeInitTree (h + 1)) := by
  refine ⟨Or.inl ?_, ?_⟩
  · have hle := Ctree.size_le (initTree_proper (h + 1))
    have hpos : 0 < 3 ^ (h + 1) := Nat.pow_pos (by omega)
    have heq : (3 : ℕ) ^ (h + 2) = 3 ^ (h + 1) * 3 := pow_succ 3 (h + 1)
    omega
  · intro et hp
    rcases hp with hPet | ⟨e, hne⟩
    · exact Or.inl (hPctr et hPet)
    right
    by_contra hz
    obtain ⟨w, hgw, hmw⟩ :=
      (matchCount_ne_zero_iff et (Gtree.mem (gtreeInitTree (h + 1))) []).mp hz
    rw [mem_gtreeInitTree, initGtreeSpec, gspec, Bool.and_eq_true, beq_iff_eq] at hgw
    obtain ⟨hwlen, hwbal⟩ := hgw
    have hmg : matchg [] (completeTrace et) (cgram 0 false w) = true := by
      rw [matchg_completeTrace et w hwbal]; exact hmw
    have hz0 : (0 : Color) ∉ completeTrace et := matchg_notMem_zero _ [] _ hmg
    refine hne ?_
    have hlen : ((evenize et).map (EdgePerm.edgeRot e)).length = h + 1 := by
      rw [List.length_map, evenize, List.length_map, ← matchpg_length et [] w hmw, hwlen]
    have hev : evenTrace ((evenize et).map (EdgePerm.edgeRot e)) = true := by
      rw [evenTrace_map_rot (edgeRot_eq_rot e), evenTrace_evenize]
    have hmem0 : (0 : Color) ∉ completeTrace ((evenize et).map (EdgePerm.edgeRot e)) := by
      rw [map_completeTrace, mem_zero_map, evenize, map_completeTrace, mem_zero_map]
      exact hz0
    rw [Ctree.mem_iff_sub_ne_zero, sub_initTree, ite_eq_left ⟨hlen, hmem0, hev⟩]
    have := dyck_countHi_pos (sum_completeTrace ((evenize et).map (EdgePerm.edgeRot e)))
    omega

/-- Every edge permutation is a rotation, or `e132` times one. -/
theorem exists_edgeRot (k : EdgePerm) :
    ∃ e : Color, EdgePerm.edgeRot e = k ∨ EdgePerm.edgeRot e = EdgePerm.e132 * k := by
  match k with
  | .e123 => exact ⟨Color.c1, by decide⟩
  | .e132 => exact ⟨Color.c1, by decide⟩
  | .e213 => exact ⟨Color.c2, by decide⟩
  | .e231 => exact ⟨Color.c3, by decide⟩
  | .e312 => exact ⟨Color.c2, by decide⟩
  | .e321 => exact ⟨Color.c3, by decide⟩

/-- The reference's `Kempe_completeP`: once the loop has converged, the even
traces the colouring tree has dropped are exactly those of the Kempe
co-closure. -/
theorem not_mem_iff_kempeCoclosure {h : ℕ} {P : List Color → Prop} {ctu ctr : Ctree}
    {gtr gtu : Gtree} (hv : KempeValid h P ctu ctr gtr gtu)
    (hcp : KempeComplete P 1 ctu ctr gtr gtu) {et0 : List Color} (hlen : et0.length = h + 1) :
    Ctree.mem ctu (evenize et0) = false ↔ KempeCoclosure P (completeTrace et0) := by
  refine ⟨fun hm => kempeCoclosure_of_not_mem hv hlen hm, fun hco => ?_⟩
  rcases hcp.progress with hlt | ⟨hctr0, hgtr0⟩
  · rw [Ctree.size_eq_zero hv.proper (by omega)]; simp
  have hacc := hcp.accounted
  have hgrz : ∀ et, Gtree.sub gtr [] et = 0 := fun et =>
    matchCount_eq_zero et (Gtree.mem gtr) [] fun w => by simpa using hgtr0 w
  have hDctu : ∀ et, Ctree.sub ctu et = if evenTrace et then Gtree.sub gtu [] et else 0 := by
    intro et; rw [hv.sub et, hgrz et, Nat.zero_add]
  have hDeven : ∀ et, Ctree.sub ctu (evenize et) = Gtree.sub gtu [] (evenize et) := by
    intro et; rw [hDctu, ite_eq_left (evenTrace_evenize et)]
  have hctu0 : ∀ et, Gtree.sub gtu [] et = 0 → Ctree.mem ctu et = false := by
    intro et hz
    have h1 : Ctree.sub ctu et = 0 := by
      rw [hDctu et, hz]
      cases evenTrace et <;> rfl
    simp [Ctree.mem, h1]
  have hgtu132 : ∀ et, Gtree.sub gtu [] et = 0 →
      Gtree.sub gtu [] (et.map EdgePerm.e132) = 0 := by
    intro et hz
    by_contra hne
    obtain ⟨w, hgw, hmw⟩ :=
      (matchCount_ne_zero_iff (et.map EdgePerm.e132) (Gtree.mem gtu) []).mp hne
    have hflip : matchpg [] (et.map EdgePerm.e132) w = matchpg [] et w := by
      simpa using matchpg_map_e132 et [] w
    rw [hflip] at hmw
    exact absurd hz ((matchCount_ne_zero_iff et (Gtree.mem gtu) []).mpr ⟨w, hgw, hmw⟩)
  have hctu132 : ∀ et, Ctree.mem ctu ((evenize et).map EdgePerm.e132) = true →
      Ctree.mem ctu (evenize et) = true := by
    intro et hm
    by_contra hn
    have hz : Gtree.sub gtu [] (evenize et) = 0 := by
      rw [← hDeven et]
      simpa [Ctree.mem] using hn
    rw [hctu0 _ (hgtu132 _ hz)] at hm
    simp at hm
  have hPctue : ∀ et, Ctree.mem ctu (evenize et) =
      (Ctree.mem ctu et || Ctree.mem ctu (et.map EdgePerm.e132)) := by
    intro et
    have hk := hctu132 et
    by_cases he : evenTrace et = true
    · rw [evenize, evenPerm, ite_eq_left he, map_one_edgePerm] at hk ⊢
      cases h1 : Ctree.mem ctu et <;>
        cases h2 : Ctree.mem ctu (et.map EdgePerm.e132) <;> simp_all
    · rw [evenize, evenPerm, ite_eq_right he, map_map_edgePerm,
        show (EdgePerm.e132 * EdgePerm.e132 : EdgePerm) = 1 by decide,
        map_one_edgePerm] at hk
      rw [evenize, evenPerm, ite_eq_right he]
      cases h1 : Ctree.mem ctu et <;>
        cases h2 : Ctree.mem ctu (et.map EdgePerm.e132) <;> simp_all
  by_contra hmem
  have hmem0 : Ctree.mem ctu (evenize et0) = true := by simpa using hmem
  have hQclosed : KempeClosed (fun cet => ∃ et, cet = completeTrace et ∧
      Ctree.mem ctu (evenize et) = true) := by
    rintro cet ⟨et, rfl, hmet⟩
    constructor
    · intro g
      refine ⟨et.map g, (map_completeTrace g et).symm, ?_⟩
      by_contra hn
      have hn' : Ctree.mem ctu (evenize (et.map g)) = false := by simpa using hn
      rw [hPctue] at hn'
      simp only [Bool.or_eq_false_iff] at hn'
      obtain ⟨hn1, hn2⟩ := hn'
      have hmapg2 : (evenize et).map (g * (evenPerm et)⁻¹) = et.map g := by
        rw [evenize, map_map_edgePerm, inv_mul_cancel_right]
      obtain ⟨e, he⟩ := exists_edgeRot (g * (evenPerm et)⁻¹)
      have hkey : ¬ Ctree.mem ctu ((evenize et).map (EdgePerm.edgeRot e)) := by
        rcases he with he | he
        · rw [he, hmapg2, hn1]; simp
        · rw [he, ← map_map_edgePerm, hmapg2, hn2]; simp
      have hzero : Gtree.sub gtu [] et = 0 := by
        rcases hacc et (Or.inr ⟨e, hkey⟩) with hm | hz
        · rw [hctr0] at hm; simp at hm
        · exact hz
      rw [hPctue et, hctu0 et hzero, hctu0 _ (hgtu132 et hzero)] at hmet
      simp at hmet
    · have hsne : Gtree.sub gtu [] (evenize et) ≠ 0 := by
        rw [← hDeven et]
        exact (Ctree.mem_iff_sub_ne_zero _ _).mp hmet
      obtain ⟨w, hgw, hmw⟩ :=
        (matchCount_ne_zero_iff (evenize et) (Gtree.mem gtu) []).mp hsne
      have hmw' : matchpg [] et w = true := by rwa [matchpg_evenize] at hmw
      have hspec := hv.available w hgw
      rw [initGtreeSpec, gspec, Bool.and_eq_true, beq_iff_eq] at hspec
      refine ⟨cgram 0 false w, ?_, ?_⟩
      · rw [matchg_completeTrace et w hspec.2]; exact hmw'
      · intro cet' hM
        have hsum : cet'.sum = 0 := sum_eq_zero_of_matchg hspec.2 hM
        obtain ⟨u, c, rfl⟩ : ∃ u c, cet' = u ++ [c] := by
          rcases List.eq_nil_or_concat' cet' with rfl | ⟨u, c, hc⟩
          · exfalso
            have hl := matchg_length _ [] _ hM
            simp only [List.length_nil] at hl
            exact cgram_ne_nil 0 false w (List.length_eq_zero_iff.mp hl)
          · exact ⟨u, c, hc⟩
        have hcu : c = u.sum := by
          have h1 : u.sum + c = 0 := by simpa using hsum
          have h2 : u.sum + (u.sum + c) = u.sum + 0 := by rw [h1]
          rwa [← add_assoc, Color.add_self, zero_add, add_zero] at h2
        subst hcu
        refine ⟨u, rfl, ?_⟩
        have hMu : matchpg [] u w = true := by
          rw [← matchg_completeTrace u w hspec.2]
          exact hM
        have hne : Gtree.sub gtu [] (evenize u) ≠ 0 :=
          (matchCount_ne_zero_iff _ (Gtree.mem gtu) []).mpr
            ⟨w, hgw, by rw [matchpg_evenize]; exact hMu⟩
        rw [Ctree.mem_iff_sub_ne_zero, hDeven u]
        exact hne
  obtain ⟨cet, hPcet, et', hcet, hmet'⟩ := hco _ hQclosed ⟨et0, rfl, hmem0⟩
  subst hcet
  rcases hacc et' (Or.inl hPcet) with hm | hz
  · rw [hctr0] at hm; simp at hm
  · have hz' : Gtree.sub gtu [] (evenize et') = 0 := by
      rw [evenize, evenPerm]
      by_cases he : evenTrace et' = true
      · rw [ite_eq_left he, map_one_edgePerm]; exact hz
      · rw [ite_eq_right he]; exact hgtu132 et' hz
    rw [hctu0 _ hz'] at hmet'
    simp at hmet'

/-! ### The Kempe closure tree of a configuration -/

/-- The tree the loop returns from the initial colouring and gram trees of ring
size `h + 2`, restricted by `ctr`. -/
def kempeTreeOf (h : ℕ) (ctr : Ctree) : Ctree :=
  (kempeTreeClosure h (h + 2) (initTree (h + 1)) ctr (gtreeInitTree (h + 1))).1

/-- The reference's `Kempe_treeP`, for an arbitrary restriction tree: if `ctr`
holds only traces of length `h + 1` whose completion satisfies `P`, and holds
the even form of every trace whose completion satisfies `P`, then the tree the
loop returns holds exactly the even traces outside the Kempe co-closure. -/
theorem not_mem_kempeTreeOf_iff {h : ℕ} {P : List Color → Prop} {ctr : Ctree}
    (hsound : ∀ et, Ctree.mem ctr et → P (completeTrace et) ∧ et.length = h + 1)
    (hcomplete : ∀ et, P (completeTrace et) → Ctree.mem ctr (evenize et))
    {et : List Color} (hlen : et.length = h + 1) :
    Ctree.mem (kempeTreeOf h ctr) (evenize et) = false ↔
      KempeCoclosure P (completeTrace et) := by
  obtain ⟨hvalid, hfull⟩ :=
    kempeTreeClosure_correct h P (h + 2) (initTree (h + 1)) ctr (gtreeInitTree (h + 1))
      (kempeValid_restrict hsound (kempeValid_init h P))
  refine not_mem_iff_kempeCoclosure hvalid (hfull 0 ?_) hlen
  rw [Nat.add_zero]
  exact kempeComplete_init hcomplete .empty

/-- The Kempe closure tree of a ring of the given size, restricted by `ctr`:
empty unless the ring has at least two darts.  This is the body of the
reference's `Kempe_tree`; that definition is `kempeTreeAt (cprsize cp)
(cpcolor cp)`, which awaits the port of the specification of `cpcolor`. -/
def kempeTreeAt : ℕ → Ctree → Ctree
  | h + 2, ctr => kempeTreeOf h ctr
  | _, _ => .empty

/-- Unfolding `kempeTreeAt` at a ring of size `h + 2`. -/
@[simp] theorem kempeTreeAt_add_two (h : ℕ) (ctr : Ctree) :
    kempeTreeAt (h + 2) ctr = kempeTreeOf h ctr := rfl

/-- The Kempe closure tree after `d` rounds, rather than the `h + 2` that
guarantee convergence. -/
def kempeTreeOfDepth (h d : ℕ) (ctr : Ctree) : Ctree :=
  (kempeTreeClosure h d (initTree (h + 1)) ctr (gtreeInitTree (h + 1))).1

/-- Unfolding the closure at full depth. -/
theorem kempeTreeOfDepth_add_two (h : ℕ) (ctr : Ctree) :
    kempeTreeOfDepth h (h + 2) ctr = kempeTreeOf h ctr := rfl

/-- **Soundness alone, and so at any depth**: a trace the loop has dropped lies
in the Kempe co-closure.  Only this direction is needed to certify
reducibility, and unlike the converse it rests on the loop invariant alone, not
on the loop having run to convergence — so the number of rounds can be chosen
to suit the computation rather than to guarantee closure. -/
theorem kempeCoclosure_of_not_mem_depth {h d : ℕ} {P : List Color → Prop} {ctr : Ctree}
    (hsound : ∀ et, Ctree.mem ctr et → P (completeTrace et) ∧ et.length = h + 1)
    {et : List Color} (hlen : et.length = h + 1)
    (hmem : Ctree.mem (kempeTreeOfDepth h d ctr) (evenize et) = false) :
    KempeCoclosure P (completeTrace et) := by
  obtain ⟨hvalid, -⟩ :=
    kempeTreeClosure_correct h P d (initTree (h + 1)) ctr (gtreeInitTree (h + 1))
      (kempeValid_restrict hsound (kempeValid_init h P))
  exact kempeCoclosure_of_not_mem hvalid hlen hmem

/-! ### The linear closure loop

The reference drives the closure with a fuel parameter that triples the work at
every level: `d` rounds perform `3 ^ d` restriction cycles.  That shape is what
makes the *completeness* half of the correctness statement go through — `h + 2`
rounds reach the fixpoint — but it is wasteful, because reducibility needs only
soundness, and soundness holds after any number of cycles.  So the loop can be
run instead as a plain iteration of a single cycle, with the iteration count
chosen per configuration and convergence observed rather than guaranteed.  The
saving is the difference between `3 ^ d` cycles and `d` of them.
-/

/-- One cycle of the closure loop: restrict the colouring tree by the
chromograms already deleted, then delete the chromograms that matched only what
that removed. -/
def kempeCycle (h : ℕ) (kr : Ctree × Gtree × Gtree) : Ctree × Gtree × Gtree :=
  kempeStep h (kempeTreeClosure h 0) kr

/-- `n` cycles of the closure loop. -/
def kempeIter (h : ℕ) : ℕ → Ctree × Gtree × Gtree → Ctree × Gtree × Gtree
  | 0, kr => kr
  | n + 1, kr => kempeIter h n (kempeCycle h kr)

/-- A cycle keeps the state valid. -/
theorem ktrValid_kempeCycle {h : ℕ} {P : List Color → Prop} {kr : Ctree × Gtree × Gtree}
    (hv : KtrValid h P kr) : KtrValid h P (kempeCycle h kr) :=
  (kempeStep_correct (ktcCorrect_zero h P) kr hv).1

/-- Iterating cycles keeps the state valid. -/
theorem ktrValid_kempeIter {h : ℕ} {P : List Color → Prop} :
    ∀ (n : ℕ) {kr : Ctree × Gtree × Gtree},
      KtrValid h P kr → KtrValid h P (kempeIter h n kr)
  | 0, _, hv => hv
  | n + 1, _, hv => ktrValid_kempeIter n (ktrValid_kempeCycle hv)

/-- The colouring tree after `n` cycles of the plain iteration, started from the
initial trees restricted by `ctr`. -/
def kempeTreeIter (h n : ℕ) (ctr : Ctree) : Ctree :=
  (kempeIter h n (kempeTreeClosure h 0 (initTree (h + 1)) ctr (gtreeInitTree (h + 1)))).1

/-- **Soundness of the plain iteration**, at any number of cycles: a trace the
iteration has dropped lies in the Kempe co-closure. -/
theorem kempeCoclosure_of_not_mem_iter {h n : ℕ} {P : List Color → Prop} {ctr : Ctree}
    (hsound : ∀ et, Ctree.mem ctr et → P (completeTrace et) ∧ et.length = h + 1)
    {et : List Color} (hlen : et.length = h + 1)
    (hmem : Ctree.mem (kempeTreeIter h n ctr) (evenize et) = false) :
    KempeCoclosure P (completeTrace et) :=
  kempeCoclosure_of_not_mem
    (ktrValid_kempeIter n
      (ktcCorrect_zero h P _ _ _ (kempeValid_restrict hsound (kempeValid_init h P))).1)
    hlen hmem

/-- The reference's `Kempe_treeP`, for a ring of size `h + 2`: the Kempe closure
tree holds exactly the even traces outside the Kempe co-closure of `P`. -/
theorem not_mem_kempeTreeAt_iff {h : ℕ} {P : List Color → Prop} {ctr : Ctree}
    (hsound : ∀ et, Ctree.mem ctr et → P (completeTrace et) ∧ et.length = h + 1)
    (hcomplete : ∀ et, P (completeTrace et) → Ctree.mem ctr (evenize et))
    {et : List Color} (hlen : et.length = h + 1) :
    Ctree.mem (kempeTreeAt (h + 2) ctr) (evenize et) = false ↔
      KempeCoclosure P (completeTrace et) := by
  rw [kempeTreeAt_add_two]
  exact not_mem_kempeTreeOf_iff hsound hcomplete hlen

end FourColor

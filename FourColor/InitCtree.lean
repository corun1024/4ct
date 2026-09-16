import FourColor.Ctree
import FourColor.Dyck
import FourColor.Seq

/-!
# The initial colouring tree

The full tree of all even partial traces for a given ring size is built by
dynamic programming: first the leaves are tabulated, then the subtrees of height
1, 2, … up to `h - 2`, and the final tree of height `h - 1` is assembled from
three pruned subtrees.  Subtrees of odd traces are pruned at that last stage.

The tables are lists of tree pairs.  The `i`-th pair holds the two subtrees that
can follow a trace in which `c2` and `c3` occur `i` times in total: the first
component for traces of even colour sum, the second for odd.

## Main definitions

* `initTree h` — the full tree of even partial traces at ring size `h`.
* `leafTable`, `mergeTable` — the tabulation steps.
* `prune1`, `prune2`, `prune3` — removal of the odd permutations.

## References

Gonthier's `theories/proof/initctree.v`.
-/

namespace FourColor

open Color Ctree

/-- The parity of a natural number, as a boolean. -/
def oddB (i : ℕ) : Bool := i % 2 == 1

@[simp] theorem oddB_zero : oddB 0 = false := rfl

@[simp] theorem oddB_succ (i : ℕ) : oddB (i + 1) = !oddB i := by
  have h1 : (i + 1) % 2 = (i % 2 + 1) % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [oddB, h, h1]

/-- A table of subtree pairs, indexed by the number of `c2`/`c3` occurrences. -/
abbrev CtreeTable := List (Ctree × Ctree)

/-- The subtree of a table at a given count and colour-sum parity. -/
def tableSub (tab : CtreeTable) (i : ℕ) (b : Bool) : Ctree :=
  if b then (tab.getD i (.empty, .empty)).2 else (tab.getD i (.empty, .empty)).1

/-- The leaf-multiplicity accumulator of the leaf table. -/
def addDyck : ℕ → ℕ → Ctree → Ctree
  | _, 0, t => .leaf t
  | m, n + 1, t => (List.range (m + 1)).foldl (fun acc i => addDyck (i + 1) n acc) t
termination_by _ n _ => n

theorem addDyck_zero (m : ℕ) (t : Ctree) : addDyck m 0 t = .leaf t := by
  simp [addDyck]

theorem addDyck_succ (m n : ℕ) (t : Ctree) :
    addDyck m (n + 1) t =
      (List.range (m + 1)).foldl (fun acc i => addDyck (i + 1) n acc) t := by
  simp [addDyck]

@[simp] theorem leafOf_succ (n : ℕ) : leafOf (n + 1) = .leaf (leafOf n) := rfl

/-- The key identity: `addDyck` accumulates a Dyck number onto a leaf. -/
theorem addDyck_leafOf : ∀ (n m d : ℕ),
    addDyck m n (leafOf d) = leafOf (genDyck (m + 1) (m + 2 * n) + d) := by
  intro n
  induction n with
  | zero =>
    intro m d
    rw [addDyck_zero, show m + 2 * 0 = m from by omega, genDyck_succ_self,
      show 1 + d = d + 1 from by omega]
    rfl
  | succ n ih =>
    have loop : ∀ m d, (List.range (m + 1)).foldl (fun acc i => addDyck (i + 1) n acc)
        (leafOf d) = leafOf (genDyck (m + 1) (m + 2 * n + 2) + d) := by
      intro m
      induction m with
      | zero =>
        intro d
        rw [show List.range (0 + 1) = [0] from rfl]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih 1 d]
        have key : genDyck (1 + 1) (1 + 2 * n) + d = genDyck (0 + 1) (0 + 2 * n + 2) + d := by
          have h := genDyck_succ_succ 0 (2 * n + 1)
          simp only [genDyck_zero_succ, Nat.add_zero] at h
          rw [show (1 : ℕ) + 2 * n = 2 * n + 1 from by omega,
              show (0 : ℕ) + 2 * n + 2 = 2 * n + 1 + 1 from by omega, h]
        rw [key]
      | succ m ihm =>
        intro d
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ihm d, ih (m + 2) _]
        have key : genDyck (m + 2 + 1) (m + 2 + 2 * n) + (genDyck (m + 1) (m + 2 * n + 2) + d)
            = genDyck (m + 1 + 1) (m + 1 + 2 * n + 2) + d := by
          have h := genDyck_succ_succ (m + 1) (m + 2 * n + 2)
          rw [show m + 2 + 1 = m + 1 + 2 from by omega,
              show m + 2 + 2 * n = m + 2 * n + 2 from by omega,
              show m + 1 + 2 * n + 2 = m + 2 * n + 2 + 1 from by omega, h]
          omega
        rw [key]
    intro m d
    rw [addDyck_succ, loop, show m + 2 * (n + 1) = m + 2 * n + 2 from by omega]

/-! ### The leaf table -/

/-- The tail of the leaf table, starting from a given leaf and count. -/
def leafTableFrom : Ctree → ℕ → ℕ → CtreeTable
  | _, _, 0 => []
  | lf, _, 1 => [(lf, lf)]
  | lf, n, h + 2 => (lf, lf) :: (.empty, lf) :: leafTableFrom (addDyck 2 n lf) (n + 1) h

/-- The table of nonempty leaves at a given ring size. -/
def leafTable (h : ℕ) : CtreeTable :=
  (.empty, Ctree.simpleLeaf) :: leafTableFrom Ctree.simpleLeaf 0 h

theorem leafTableFrom_length : ∀ (h : ℕ) (lf : Ctree) (n : ℕ),
    (leafTableFrom lf n h).length = h := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro lf n
    match h with
    | 0 => rfl
    | 1 => rfl
    | h + 2 => simp [leafTableFrom, ih h (by omega)]

@[simp] theorem leafTable_length (h : ℕ) : (leafTable h).length = h + 1 := by
  simp [leafTable, leafTableFrom_length]

/-! ### Merging and pruning -/

/-- Merge two adjacent table entries into the entry one level up. -/
def mergePair (p q : Ctree × Ctree) : Ctree × Ctree :=
  (Ctree.cons p.2 q.1 q.2, Ctree.cons p.1 q.2 q.1)

/-- Compute the table of subtrees one level higher. -/
def mergeTable : CtreeTable → CtreeTable
  | [] => []
  | line :: tab => pairmap mergePair line tab

/-- Prune the branches where `c2` occurs before `c1`. -/
def prune1 : Ctree → Ctree
  | .node t₁ t₂ _ => Ctree.cons (prune1 t₁) t₂ .empty
  | t => t

/-- Prune the branches where `c3` occurs before `c2`. -/
def prune2 : Ctree → Ctree
  | .node _ t₂ t₃ => Ctree.cons .empty (prune2 t₂) t₃
  | t => t

/-- Prune the branches where `c1` occurs before `c3`. -/
def prune3 : Ctree → Ctree
  | .node t₁ _ t₃ => Ctree.cons t₁ .empty (prune3 t₃)
  | t => t

/-- The full tree of all even partial traces for ring size `h`. -/
def initTree (h : ℕ) : Ctree :=
  match mergeTable^[h - 1] (leafTable h) with
  | (_, t₁) :: (t₂, t₃) :: _ => Ctree.cons (prune1 t₁) (prune2 t₂) (prune3 t₃)
  | _ => .empty

@[simp] theorem mergeTable_length (tab : CtreeTable) :
    (mergeTable tab).length = tab.length - 1 := by
  cases tab with
  | nil => rfl
  | cons line tab => simp [mergeTable]

/-! ### Leaf-table correctness -/

@[simp] theorem dyck_zero : dyck 0 = 1 := rfl

@[simp] theorem dyck_two : dyck 2 = 1 := rfl

theorem simpleLeaf_eq : Ctree.simpleLeaf = leafOf (dyck (2 * 0 + 2)) := rfl

/-- The Dyck recurrence driving the leaf table. -/
theorem dyck_step (j : ℕ) :
    addDyck 2 j (leafOf (dyck (2 * j + 2))) = leafOf (dyck (2 * (j + 1) + 2)) := by
  rw [addDyck_leafOf]
  congr 1
  have h1 := genDyck_succ_succ 0 (2 * j + 3)
  have h2 := genDyck_succ_succ 1 (2 * j + 2)
  have h3 := genDyck_succ_succ 0 (2 * j + 1)
  simp only [genDyck_zero_succ, Nat.add_zero] at h1 h3
  simp only [dyck] at *
  have e1 : 2 * (j + 1) + 2 = 2 * j + 3 + 1 := by omega
  have e2 : 2 * j + 3 = 2 * j + 2 + 1 := by omega
  have e3 : 2 + 2 * j = 2 * j + 2 := by omega
  rw [e1, h1, e2, h2, e3]

theorem leafTableFrom_even : ∀ (j h n : ℕ), 2 * j < h →
    (leafTableFrom (leafOf (dyck (2 * n + 2))) n h).getD (2 * j) (.empty, .empty)
      = (leafOf (dyck (2 * (n + j) + 2)), leafOf (dyck (2 * (n + j) + 2))) := by
  intro j
  induction j with
  | zero =>
    intro h n hh
    match h with
    | 0 => omega
    | 1 => simp [leafTableFrom]
    | _ + 2 => simp [leafTableFrom]
  | succ j ih =>
    intro h n hh
    match h with
    | 0 => omega
    | 1 => omega
    | h + 2 =>
      have harg : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [leafTableFrom, harg]
      simp only [List.getD_cons_succ]
      rw [dyck_step n, ih h (n + 1) (by omega),
        show n + 1 + j = n + (j + 1) from by omega]

theorem leafTableFrom_odd : ∀ (j h n : ℕ), 2 * j + 1 < h →
    (leafTableFrom (leafOf (dyck (2 * n + 2))) n h).getD (2 * j + 1) (.empty, .empty)
      = (.empty, leafOf (dyck (2 * (n + j) + 2))) := by
  intro j
  induction j with
  | zero =>
    intro h n hh
    match h with
    | 0 => omega
    | 1 => omega
    | _ + 2 => simp [leafTableFrom]
  | succ j ih =>
    intro h n hh
    match h with
    | 0 => omega
    | 1 => omega
    | h + 2 =>
      have harg : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
      rw [leafTableFrom, harg]
      simp only [List.getD_cons_succ]
      rw [dyck_step n, ih h (n + 1) (by omega),
        show n + 1 + j = n + (j + 1) from by omega]

/-- The leaves of the initial tree carry the right Dyck multiplicities. -/
theorem leafTable_sub {h i : ℕ} (hi : i ≤ h) (b0 : Bool) :
    tableSub (leafTable h) i b0 =
      if Color.ofBits (oddB i) b0 = 0 then .empty
      else leafOf (dyck (i + (if oddB i then 1 else 0))) := by
  obtain ⟨j, hj | hj⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
  · subst hj
    obtain _ | k := j
    · cases b0 <;> simp [tableSub, leafTable, Color.ofBits, Ctree.simpleLeaf, leafOf]
    · have hk : 2 * k + 1 < h := by omega
      have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      have hodd : oddB (2 * k + 1 + 1) = false := by
        have hm : (2 * k + 1 + 1) % 2 = 0 := by omega
        simp [oddB, hm]
      rw [tableSub, leafTable, hidx]
      simp only [List.getD_cons_succ]
      rw [simpleLeaf_eq, leafTableFrom_odd k h 0 hk, hodd,
        show 2 * (0 + k) + 2 = 2 * k + 1 + 1 from by omega]
      cases b0 <;> simp [Color.ofBits]
  · subst hj
    have hk : 2 * j < h := by omega
    have hodd : oddB (2 * j + 1) = true := by
      have hm : (2 * j + 1) % 2 = 1 := by omega
      simp [oddB, hm]
    rw [tableSub, leafTable]
    simp only [List.getD_cons_succ]
    rw [simpleLeaf_eq, leafTableFrom_even j h 0 hk, hodd,
      show 2 * (0 + j) + 2 = 2 * j + 1 + 1 from by omega]
    cases b0 <;> simp [Color.ofBits]

/-! ### Properness of the initial tree -/

theorem prune1_proper : ∀ (n : ℕ) (t : Ctree), Ctree.Proper n t → Ctree.Proper n (prune1 t) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact ht
    | .node _ _ _ => exact absurd ht not_false
  | succ n ih =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact absurd ht not_false
    | .node t₁ t₂ t₃ =>
      obtain ⟨_, h₁, h₂, _⟩ := ht
      exact Ctree.cons_proper (ih _ h₁) h₂ trivial

theorem prune2_proper : ∀ (n : ℕ) (t : Ctree), Ctree.Proper n t → Ctree.Proper n (prune2 t) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact ht
    | .node _ _ _ => exact absurd ht not_false
  | succ n ih =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact absurd ht not_false
    | .node t₁ t₂ t₃ =>
      obtain ⟨_, _, h₂, h₃⟩ := ht
      exact Ctree.cons_proper trivial (ih _ h₂) h₃

theorem prune3_proper : ∀ (n : ℕ) (t : Ctree), Ctree.Proper n t → Ctree.Proper n (prune3 t) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact ht
    | .node _ _ _ => exact absurd ht not_false
  | succ n ih =>
    intro t ht
    match t with
    | .empty => trivial
    | .leaf _ => exact absurd ht not_false
    | .node t₁ t₂ t₃ =>
      obtain ⟨_, h₁, _, h₃⟩ := ht
      exact Ctree.cons_proper h₁ trivial (ih _ h₃)

/-- One merge step reads two adjacent table entries. -/
theorem tableSub_mergeTable (tab : CtreeTable) (i : ℕ) (hi : i + 1 < tab.length)
    (b : Bool) :
    tableSub (mergeTable tab) i b =
      if b then Ctree.cons (tableSub tab i false) (tableSub tab (i + 1) true)
        (tableSub tab (i + 1) false)
      else Ctree.cons (tableSub tab i true) (tableSub tab (i + 1) false)
        (tableSub tab (i + 1) true) := by
  cases tab with
  | nil => simp at hi
  | cons line tab =>
    rw [mergeTable, tableSub, tableSub, tableSub,
      getD_pairmap mergePair line tab (.empty, .empty) (.empty, .empty) i (by simpa using hi)]
    cases b <;> rfl

/-- The invariant maintained by the tabulation. -/
theorem mergeTable_iterate : ∀ (n h : ℕ), n ≤ h →
    (mergeTable^[n] (leafTable h)).length = h + 1 - n ∧
      ∀ i b, i < (mergeTable^[n] (leafTable h)).length →
        Ctree.Proper n (tableSub (mergeTable^[n] (leafTable h)) i b) := by
  intro n
  induction n with
  | zero =>
    intro h _
    refine ⟨by simp, fun i b hi => ?_⟩
    have hi' : i ≤ h := by
      rw [Function.iterate_zero, id_eq, leafTable_length] at hi
      omega
    simp only [Function.iterate_zero, id_eq]
    rw [leafTable_sub hi']
    split
    · trivial
    · exact Ctree.proper_leafOf _
  | succ n ih =>
    intro h hn
    obtain ⟨hlen, hprop⟩ := ih h (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [mergeTable_length, hlen]; omega, fun i b hi => ?_⟩
    rw [mergeTable_length, hlen] at hi
    have hi1 : i + 1 < (mergeTable^[n] (leafTable h)).length := by rw [hlen]; omega
    rw [tableSub_mergeTable _ _ hi1]
    cases b <;>
      exact Ctree.cons_proper (hprop _ _ (by omega)) (hprop _ _ hi1) (hprop _ _ hi1)

/-- The initial tree is a proper tree of the ring height. -/
theorem initTree_proper (h : ℕ) : Ctree.Proper h (initTree h) := by
  match h with
  | 0 => trivial
  | h + 1 =>
    obtain ⟨hlen, hprop⟩ := mergeTable_iterate h (h + 1) (by omega)
    have hlen2 : (mergeTable^[h] (leafTable (h + 1))).length = 2 := by omega
    rw [initTree, Nat.add_sub_cancel]
    match hm : mergeTable^[h] (leafTable (h + 1)) with
    | [] => rw [hm] at hlen2; simp at hlen2
    | [_] => rw [hm] at hlen2; simp at hlen2
    | (t₀, t₁) :: (t₂, t₃) :: rest =>
      have h1 : Ctree.Proper h t₁ := by
        have hx := hprop 0 true (by rw [hlen2]; omega)
        rw [tableSub, hm] at hx
        simpa using hx
      have h2 : Ctree.Proper h t₂ := by
        have hx := hprop 1 false (by rw [hlen2]; omega)
        rw [tableSub, hm] at hx
        simpa using hx
      have h3 : Ctree.Proper h t₃ := by
        have hx := hprop 1 true (by rw [hlen2]; omega)
        rw [tableSub, hm] at hx
        simpa using hx
      exact Ctree.cons_proper (prune1_proper h t₁ h1) (prune2_proper h t₂ h2)
        (prune3_proper h t₃ h3)

/-! ### Pruning implements the evenness condition -/

theorem sub_prune1 : ∀ (et : List Color) (t : Ctree),
    Ctree.sub (prune1 t) et = if evenTail et then Ctree.sub t et else 0 := by
  intro et
  induction et with
  | nil =>
    intro t
    match t with
    | .empty => rfl
    | .leaf _ => rfl
    | .node t₁ t₂ t₃ => simp only [prune1, Ctree.sub_cons, Ctree.sub_node_nil, ite_self]
  | cons e et ih =>
    intro t
    match t with
    | .empty => cases e <;> simp only [prune1, Ctree.sub_empty, ite_self]
    | .leaf _ => cases e <;> simp only [prune1, Ctree.sub_leaf_cons, ite_self]
    | .node t₁ t₂ t₃ =>
      rw [prune1]
      cases e <;> simp only [Ctree.sub_cons_eq_sub_sel, Ctree.sel_cons, Ctree.sel_zero,
        Ctree.sel_node_c1, Ctree.sel_node_c2, Ctree.sel_node_c3, evenTail_cons, evenStep]
      · simp
      · exact ih t₁
      · simp
      · simp

theorem sub_prune2 : ∀ (et : List Color) (t : Ctree),
    Ctree.sub (prune2 t) et =
      if evenTail (et.map EdgePerm.e312) then Ctree.sub t et else 0 := by
  intro et
  induction et with
  | nil =>
    intro t
    match t with
    | .empty => rfl
    | .leaf _ => rfl
    | .node t₁ t₂ t₃ => simp only [prune2, Ctree.sub_cons, Ctree.sub_node_nil, ite_self]
  | cons e et ih =>
    intro t
    match t with
    | .empty => cases e <;> simp only [prune2, Ctree.sub_empty, ite_self]
    | .leaf _ => cases e <;> simp only [prune2, Ctree.sub_leaf_cons, ite_self]
    | .node t₁ t₂ t₃ =>
      rw [prune2]
      cases e <;> simp only [Ctree.sub_cons_eq_sub_sel, Ctree.sel_cons, Ctree.sel_zero,
        Ctree.sel_node_c1, Ctree.sel_node_c2, Ctree.sel_node_c3, List.map_cons,
        EdgePerm.apply, evenTail_cons, evenStep]
      · simp
      · simp
      · exact ih t₂
      · simp

theorem sub_prune3 : ∀ (et : List Color) (t : Ctree),
    Ctree.sub (prune3 t) et =
      if evenTail (et.map EdgePerm.e231) then Ctree.sub t et else 0 := by
  intro et
  induction et with
  | nil =>
    intro t
    match t with
    | .empty => rfl
    | .leaf _ => rfl
    | .node t₁ t₂ t₃ => simp only [prune3, Ctree.sub_cons, Ctree.sub_node_nil, ite_self]
  | cons e et ih =>
    intro t
    match t with
    | .empty => cases e <;> simp only [prune3, Ctree.sub_empty, ite_self]
    | .leaf _ => cases e <;> simp only [prune3, Ctree.sub_leaf_cons, ite_self]
    | .node t₁ t₂ t₃ =>
      rw [prune3]
      cases e <;> simp only [Ctree.sub_cons_eq_sub_sel, Ctree.sel_cons, Ctree.sel_zero,
        Ctree.sel_node_c1, Ctree.sel_node_c2, Ctree.sel_node_c3, List.map_cons,
        EdgePerm.apply, evenTail_cons, evenStep]
      · simp
      · simp
      · simp
      · exact ih t₃

/-! ### The trace-count invariant -/

/-- The completion of a partial trace in a table context. -/
abbrev closeAt (i : ℕ) (b0 : Bool) (et : List Color) : List Color :=
  et ++ [Color.ofBits (oddB i) b0 + et.sum]

theorem closeAt_c1 (i : ℕ) (b0 : Bool) (et : List Color) :
    closeAt i b0 (Color.c1 :: et) = Color.c1 :: closeAt i (!b0) et := by
  have key : Color.ofBits (oddB i) b0 + Color.c1 = Color.ofBits (oddB i) (!b0) := by
    cases hb : oddB i <;> cases b0 <;> (simp only [Color.ofBits]; decide)
  simp only [closeAt, List.cons_append, List.sum_cons]
  congr 2
  rw [← add_assoc, key]

theorem closeAt_c2 (i : ℕ) (b0 : Bool) (et : List Color) :
    closeAt i b0 (Color.c2 :: et) = Color.c2 :: closeAt (i + 1) b0 et := by
  have key : Color.ofBits (oddB i) b0 + Color.c2 = Color.ofBits (oddB (i + 1)) b0 := by
    simp only [oddB_succ]
    cases hb : oddB i <;> cases b0 <;> (simp only [Color.ofBits]; decide)
  simp only [closeAt, List.cons_append, List.sum_cons]
  congr 2
  rw [← add_assoc, key]

theorem closeAt_c3 (i : ℕ) (b0 : Bool) (et : List Color) :
    closeAt i b0 (Color.c3 :: et) = Color.c3 :: closeAt (i + 1) (!b0) et := by
  have key : Color.ofBits (oddB i) b0 + Color.c3 = Color.ofBits (oddB (i + 1)) (!b0) := by
    simp only [oddB_succ]
    cases hb : oddB i <;> cases b0 <;> (simp only [Color.ofBits]; decide)
  simp only [closeAt, List.cons_append, List.sum_cons]
  congr 2
  rw [← add_assoc, key]

@[simp] theorem countHi_cons_c1 (l : List Color) : countHi (Color.c1 :: l) = countHi l := by
  simp [countHi, List.countP_cons]

@[simp] theorem countHi_cons_c2 (l : List Color) : countHi (Color.c2 :: l) = countHi l + 1 := by
  simp [countHi, List.countP_cons]

@[simp] theorem countHi_cons_c3 (l : List Color) : countHi (Color.c3 :: l) = countHi l + 1 := by
  simp [countHi, List.countP_cons]

theorem hi_ofBits (i : ℕ) (b0 : Bool) : (Color.ofBits (oddB i) b0).hi = oddB i := by
  cases hb : oddB i <;> cases b0 <;> (simp only [Color.ofBits]; decide)

/-- The shape of one inductive step, shared by the three nonzero colours. -/
private theorem step_eq {n i i' : ℕ} {b0 b0' : Bool} {e : Color} {et : List Color}
    (he : e ≠ 0) (hclose : closeAt i b0 (e :: et) = e :: closeAt i' b0' et)
    (hcount : i' + countHi (closeAt i' b0' et) = i + countHi (e :: closeAt i' b0' et)) :
    (if et.length = n ∧ (0 : Color) ∉ closeAt i' b0' et
        then dyck (i' + countHi (closeAt i' b0' et)) else 0)
      = if (e :: et).length = n + 1 ∧ (0 : Color) ∉ closeAt i b0 (e :: et)
        then dyck (i + countHi (closeAt i b0 (e :: et))) else 0 := by
  rw [hclose, hcount]
  refine (if_congr ?_ rfl rfl).symm
  simp only [List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, not_or]
  exact and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨fun hc => he hc.symm, h⟩⟩

theorem mergeTable_iterate_sub : ∀ (n h : ℕ), n ≤ h →
    ∀ i b0, i < (mergeTable^[n] (leafTable h)).length → ∀ et : List Color,
      Ctree.sub (tableSub (mergeTable^[n] (leafTable h)) i b0) et =
        if et.length = n ∧ (0 : Color) ∉ closeAt i b0 et
        then dyck (i + countHi (closeAt i b0 et)) else 0 := by
  intro n
  induction n with
  | zero =>
    intro h _ i b0 hi et
    have hi' : i ≤ h := by
      rw [Function.iterate_zero, id_eq, leafTable_length] at hi; omega
    simp only [Function.iterate_zero, id_eq]
    rw [leafTable_sub hi']
    cases et with
    | cons e et =>
      have hcond : ¬((e :: et).length = 0 ∧ (0 : Color) ∉ closeAt i b0 (e :: et)) := by
        rintro ⟨hl, -⟩; simp at hl
      rw [if_neg hcond]
      split
      · simp
      · rw [Ctree.sub_leafOf]; simp
    | nil =>
      have hclose : closeAt i b0 [] = [Color.ofBits (oddB i) b0] := by simp [closeAt]
      rw [hclose]
      split
      · rename_i hc
        rw [hc]
        simp
      · rename_i hc
        have hcond : ([] : List Color).length = 0 ∧
            (0 : Color) ∉ [Color.ofBits (oddB i) b0] := by
          refine ⟨rfl, ?_⟩
          intro hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          exact hc hmem.symm
        rw [Ctree.sub_leafOf, ite_eq_left (rfl : ([] : List Color) = []),
          ite_eq_left hcond]
        congr 2
        simp [countHi, hi_ofBits]
  | succ n ih =>
    intro h hn i b0 hi et
    have hlen := (mergeTable_iterate n h (by omega)).1
    rw [Function.iterate_succ_apply'] at hi ⊢
    rw [mergeTable_length, hlen] at hi
    have hi1 : i + 1 < (mergeTable^[n] (leafTable h)).length := by rw [hlen]; omega
    have hi0 : i < (mergeTable^[n] (leafTable h)).length := by omega
    rw [tableSub_mergeTable _ _ hi1]
    cases et with
    | nil => cases b0 <;> simp [closeAt]
    | cons e et =>
      cases e with
      | c0 =>
        cases b0 <;>
          simp only [ite_true, ite_false, Bool.false_eq_true, Ctree.sub_cons,
            Ctree.sub_cons_eq_sub_sel, Ctree.sel_cons, Color.c0_eq_zero, Ctree.sel_zero,
            Ctree.sub_empty] <;>
          rw [if_neg (by rintro ⟨-, hmem⟩; exact hmem (by simp [closeAt]))]
      | c1 =>
        cases b0 <;>
          simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
            Bool.false_eq_true, Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel,
            Ctree.sel_cons, Ctree.sel_node_c1] <;>
          rw [ih h (by omega) i _ hi0 et] <;>
          exact step_eq (by decide) (closeAt_c1 i _ et) (by simp only [countHi_cons_c1])
      | c2 =>
        cases b0 <;>
          simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
            Bool.false_eq_true, Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel,
            Ctree.sel_cons, Ctree.sel_node_c2] <;>
          rw [ih h (by omega) (i + 1) _ hi1 et] <;>
          exact step_eq (by decide) (closeAt_c2 i _ et) (by simp only [countHi_cons_c2]; omega)
      | c3 =>
        cases b0 <;>
          simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
            Bool.false_eq_true, Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel,
            Ctree.sel_cons, Ctree.sel_node_c3] <;>
          rw [ih h (by omega) (i + 1) _ hi1 et] <;>
          exact step_eq (by decide) (closeAt_c3 i _ et) (by simp only [countHi_cons_c3]; omega)

/-! ### Correctness of the initial tree -/

private theorem ite_ite_eq (p q : Prop) [Decidable p] [Decidable q] (a : ℕ) :
    (if p then (if q then a else 0) else 0) = if q ∧ p then a else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem completeTrace_cons (e : Color) (et : List Color) :
    completeTrace (e :: et) = e :: (et ++ [e + et.sum]) := by
  simp [completeTrace]

/-- The initial tree contains exactly the proper even traces of the ring size,
each with its Dyck multiplicity. -/
theorem sub_initTree (h : ℕ) (et : List Color) :
    Ctree.sub (initTree h) et =
      if et.length = h ∧ (0 : Color) ∉ completeTrace et ∧ evenTrace et = true
      then dyck (countHi (completeTrace et)) else 0 := by
  match h with
  | 0 =>
    have hinit : initTree 0 = .empty := by
      rw [initTree]
      have : leafTable 0 = [(Ctree.empty, Ctree.simpleLeaf)] := rfl
      simp [this]
    rw [hinit, Ctree.sub_empty]
    cases et with
    | cons e et => rw [if_neg (by rintro ⟨hl, -⟩; simp at hl)]
    | nil =>
      rw [if_neg (by rintro ⟨-, hm, -⟩; exact hm (by simp [completeTrace]))]
  | h + 1 =>
    obtain ⟨hlen, -⟩ := mergeTable_iterate h (h + 1) (by omega)
    have hsub := mergeTable_iterate_sub h (h + 1) (by omega)
    have hlen2 : (mergeTable^[h] (leafTable (h + 1))).length = 2 := by omega
    rw [initTree, Nat.add_sub_cancel]
    match hm : mergeTable^[h] (leafTable (h + 1)) with
    | [] => rw [hm] at hlen2; simp at hlen2
    | [_] => rw [hm] at hlen2; simp at hlen2
    | (t₀, t₁) :: (t₂, t₃) :: rest =>
      have e₁ : Ctree.sub t₁ = fun et => if et.length = h ∧ (0 : Color) ∉ closeAt 0 true et
          then dyck (0 + countHi (closeAt 0 true et)) else 0 := by
        funext u
        have hx := hsub 0 true (by rw [hlen2]; omega) u
        rwa [tableSub, hm] at hx
      have e₂ : Ctree.sub t₂ = fun et => if et.length = h ∧ (0 : Color) ∉ closeAt 1 false et
          then dyck (1 + countHi (closeAt 1 false et)) else 0 := by
        funext u
        have hx := hsub 1 false (by rw [hlen2]; omega) u
        rwa [tableSub, hm] at hx
      have e₃ : Ctree.sub t₃ = fun et => if et.length = h ∧ (0 : Color) ∉ closeAt 1 true et
          then dyck (1 + countHi (closeAt 1 true et)) else 0 := by
        funext u
        have hx := hsub 1 true (by rw [hlen2]; omega) u
        rwa [tableSub, hm] at hx
      cases et with
      | nil =>
        rw [if_neg (by rintro ⟨hl, -⟩; simp at hl)]
        simp
      | cons e et =>
        have hclose : ∀ c : Color, completeTrace (c :: et) = c :: (et ++ [c + et.sum]) :=
          fun c => completeTrace_cons c et
        cases e with
        | c0 =>
          rw [if_neg (by rintro ⟨-, hmem, -⟩; exact hmem (by simp [hclose]))]
          simp
        | c1 =>
          have hcl : closeAt 0 true et = et ++ [Color.c1 + et.sum] := by
            simp [closeAt, Color.ofBits]
          have hnt : evenTrace (Color.c1 :: et) = evenTail et := by
            simp [evenTrace, normTail, EdgePerm.rotTo]
          rw [Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel, Ctree.sel_node_c1,
            sub_prune1 et t₁, e₁, ite_ite_eq, hcl, hclose, hnt]
          refine if_congr ?_ ?_ rfl
          · constructor
            · rintro ⟨⟨hl, hm⟩, hev⟩
              refine ⟨by simpa using hl, ?_, hev⟩
              simp only [List.mem_cons, not_or]
              exact ⟨by decide, hm⟩
            · rintro ⟨hl, hm, hev⟩
              simp only [List.mem_cons, not_or] at hm
              exact ⟨⟨by simpa using hl, hm.2⟩, hev⟩
          · congr 1
            simp only [countHi_cons_c1]
            omega
        | c2 =>
          have hcl : closeAt 1 false et = et ++ [Color.c2 + et.sum] := by
            simp [closeAt, Color.ofBits]
          have hnt : evenTrace (Color.c2 :: et) =
              evenTail (et.map EdgePerm.e312) := by
            simp [evenTrace, normTail, EdgePerm.rotTo]
          rw [Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel, Ctree.sel_node_c2,
            sub_prune2 et t₂, e₂, ite_ite_eq, hcl, hclose, hnt]
          refine if_congr ?_ ?_ rfl
          · constructor
            · rintro ⟨⟨hl, hm⟩, hev⟩
              refine ⟨by simpa using hl, ?_, hev⟩
              simp only [List.mem_cons, not_or]
              exact ⟨by decide, hm⟩
            · rintro ⟨hl, hm, hev⟩
              simp only [List.mem_cons, not_or] at hm
              exact ⟨⟨by simpa using hl, hm.2⟩, hev⟩
          · congr 1
            simp only [countHi_cons_c2]
            omega
        | c3 =>
          have hcl : closeAt 1 true et = et ++ [Color.c3 + et.sum] := by
            simp [closeAt, Color.ofBits]
          have hnt : evenTrace (Color.c3 :: et) =
              evenTail (et.map EdgePerm.e231) := by
            simp [evenTrace, normTail, EdgePerm.rotTo]
          rw [Ctree.sub_cons, Ctree.sub_cons_eq_sub_sel, Ctree.sel_node_c3,
            sub_prune3 et t₃, e₃, ite_ite_eq, hcl, hclose, hnt]
          refine if_congr ?_ ?_ rfl
          · constructor
            · rintro ⟨⟨hl, hm⟩, hev⟩
              refine ⟨by simpa using hl, ?_, hev⟩
              simp only [List.mem_cons, not_or]
              exact ⟨by decide, hm⟩
            · rintro ⟨hl, hm, hev⟩
              simp only [List.mem_cons, not_or] at hm
              exact ⟨⟨by simpa using hl, hm.2⟩, hev⟩
          · congr 1
            simp only [countHi_cons_c3]
            omega

end FourColor

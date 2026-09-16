import FourColor.CfColor

/-!
# The colouring tree as an explicit list fold

`cpcolor cp` is built by folding the construction program over `cpcolor1`, a
functional whose every case is a finite union of recursive calls on explicitly
enumerated traces.  Collecting those traces into a list turns the whole fold
into a list computation: `foldList cp ts` is the list of traces reached from
`ts` by running the program, and membership in the tree is membership in the
list of branches it produces.

This is the bridge to the bulk bitmask computation: the bitmask code will
compute with `foldList`, and this file is what relates it back to `Ctree`.

## Main definitions

* `enum1 s et` — the traces one construction step enumerates from `et`.
* `foldList cp ts` — the traces reached by running `cp` (head first) on `ts`.
* `finalTraces cp` — the traces `cpcolor0 cp` folds over, symmetry cases
  included.
* `foldHeight cp n` — the height of the tree the fold of `cp` produces from a
  trace of length `n`; only needed to know that the unions in `cpcolor1` are
  unions of trees of equal height.

## Main results

* `mem_cpcolor1` — one step of the fold enumerates exactly `enum1`.
* `mem_foldr_cpcolor1`, `mem_cpcolor0` — the same for the whole fold.
* `sum_finalTraces`, `zero_notMem_finalTraces`, `two_le_length_finalTraces` —
  the invariants of the enumerated traces.
* `mem_cpcolor_iff` — **the specification of the colouring tree as a fold**.
-/

namespace FourColor
namespace Bulk

open Color EdgePerm

/-! ### The traces enumerated by one step -/

/-- The traces one construction step enumerates, mirroring `cpcolor1`: the trees
`cpcolor1 s f et` unions are exactly `f t` for `t` in this list. -/
def enum1 (s : CpStep) (et : List Color) : List (List Color) :=
  match s, et with
  | .R n, _ => [et.rotate n]
  | .R', _ => if et.length ≤ 1 then [] else [et.rotate (et.length - 1)]
  | .U, _ => [c1 :: c1 :: et, c2 :: c2 :: et, c3 :: c3 :: et]
  | .Y, e₁ :: et' => [e231 e₁ :: e312 e₁ :: et', e312 e₁ :: e231 e₁ :: et']
  | .K, e₁ :: e₂ :: et' => if e₁ = e₂ then [] else [(e₁ + e₂) :: et']
  | .H, e₁ :: e₂ :: et' =>
      if e₁ = e₂ then [e231 e₁ :: e231 e₁ :: et', e312 e₁ :: e312 e₁ :: et']
      else [e₂ :: e₁ :: et']
  | .A, e₁ :: e₂ :: et' =>
      if e₁ = e₂ then [match et' with | [] => [e₁, e₂] | _ :: _ => et'] else []
  | _, _ => []

@[simp] theorem enum1_R (n : ℕ) (et : List Color) : enum1 (.R n) et = [et.rotate n] := rfl

@[simp] theorem enum1_R' (et : List Color) :
    enum1 .R' et = if et.length ≤ 1 then [] else [et.rotate (et.length - 1)] := rfl

@[simp] theorem enum1_U (et : List Color) :
    enum1 .U et = [c1 :: c1 :: et, c2 :: c2 :: et, c3 :: c3 :: et] := rfl

@[simp] theorem enum1_Y_nil : enum1 .Y [] = [] := rfl

@[simp] theorem enum1_Y_cons (e₁ : Color) (et : List Color) :
    enum1 .Y (e₁ :: et) = [e231 e₁ :: e312 e₁ :: et, e312 e₁ :: e231 e₁ :: et] := rfl

@[simp] theorem enum1_K_nil : enum1 .K [] = [] := rfl

@[simp] theorem enum1_K_singleton (e₁ : Color) : enum1 .K [e₁] = [] := rfl

@[simp] theorem enum1_K_cons (e₁ e₂ : Color) (et : List Color) :
    enum1 .K (e₁ :: e₂ :: et) = if e₁ = e₂ then [] else [(e₁ + e₂) :: et] := rfl

@[simp] theorem enum1_H_nil : enum1 .H [] = [] := rfl

@[simp] theorem enum1_H_singleton (e₁ : Color) : enum1 .H [e₁] = [] := rfl

@[simp] theorem enum1_H_cons (e₁ e₂ : Color) (et : List Color) :
    enum1 .H (e₁ :: e₂ :: et) =
      if e₁ = e₂ then [e231 e₁ :: e231 e₁ :: et, e312 e₁ :: e312 e₁ :: et]
      else [e₂ :: e₁ :: et] := rfl

@[simp] theorem enum1_A_nil : enum1 .A [] = [] := rfl

@[simp] theorem enum1_A_singleton (e₁ : Color) : enum1 .A [e₁] = [] := rfl

@[simp] theorem enum1_A_cons (e₁ e₂ : Color) (et : List Color) :
    enum1 .A (e₁ :: e₂ :: et) =
      if e₁ = e₂ then [match et with | [] => [e₁, e₂] | _ :: _ => et] else [] := rfl

/-! ### Heights

The unions in `cpcolor1` are always unions of the trees of traces of the same
length, so they are unions of `Ctree`s of the same height; `Ctree.mem_union`
needs exactly that. -/

/-- The height of the tree `List.foldr cpcolor1 cpbranch cp` produces from a
trace of length `n`. -/
def foldHeight : CProg → ℕ → ℕ
  | [], n => n - 2
  | .R _ :: cp, n => foldHeight cp n
  | .R' :: cp, n => foldHeight cp n
  | .U :: cp, n => foldHeight cp (n + 2)
  | .Y :: cp, n => foldHeight cp (n + 1)
  | .K :: cp, n => foldHeight cp (n - 1)
  | .H :: cp, n => foldHeight cp n
  | .A :: cp, n => foldHeight cp (if n = 2 then 2 else n - 2)

/-- An improper trace normalises to the failure value. -/
theorem evenNormTail_of_not_properTrace {u : List Color} (h : ¬ ProperTrace u) :
    evenNormTail u = [0] := by
  cases u with
  | nil => simp [evenNormTail, normTail]
  | cons c t =>
    have hc : c = 0 := by by_contra hne; exact h hne
    simp [evenNormTail, normTail, hc]

/-- The leaf of the fold has the height predicted by the length of its trace. -/
theorem proper_cpbranch (u : List Color) : Ctree.Proper (u.length - 2) (cpbranch u) := by
  rw [cpbranch_spec]
  by_cases hp : ProperTrace u.tail
  · refine Ctree.ofTrace_proper ?_
    rw [length_evenNormTail_of_properTrace hp, List.length_tail]
    omega
  · rw [evenNormTail_of_not_properTrace hp]
    show Ctree.Proper (u.length - 2) Ctree.empty
    trivial

/-- Every tree the fold produces is proper, of the height predicted by the
length of the trace. -/
theorem proper_foldr : ∀ (cp : CProg) (u : List Color),
    Ctree.Proper (foldHeight cp u.length) (List.foldr cpcolor1 cpbranch cp u) := by
  intro cp
  induction cp with
  | nil => exact proper_cpbranch
  | cons s cp ih =>
    have key : ∀ (v : List Color) (m : ℕ), v.length = m →
        Ctree.Proper (foldHeight cp m) (List.foldr cpcolor1 cpbranch cp v) := by
      intro v m hm; rw [← hm]; exact ih v
    intro u
    rw [List.foldr_cons]
    cases s with
    | R n =>
      rw [cpcolor1_R, foldHeight]
      exact key _ _ (List.length_rotate ..)
    | R' =>
      rw [cpcolor1_R', foldHeight]
      split
      · trivial
      · exact key _ _ (List.length_rotate ..)
    | U =>
      rw [cpcolor1_U, foldHeight]
      exact Ctree.union_proper _ _ _ (key _ _ (by simp))
        (Ctree.union_proper _ _ _ (key _ _ (by simp)) (key _ _ (by simp)))
    | Y =>
      rw [foldHeight]
      cases u with
      | nil => trivial
      | cons e₁ u =>
        rw [cpcolor1_Y_cons]
        exact Ctree.union_proper _ _ _ (key _ _ (by simp)) (key _ _ (by simp))
    | K =>
      rw [foldHeight]
      match u with
      | [] => trivial
      | [_] => trivial
      | e₁ :: e₂ :: u =>
        rw [cpcolor1_K_cons]
        split
        · trivial
        · exact key _ _ (by simp)
    | H =>
      rw [foldHeight]
      match u with
      | [] => trivial
      | [_] => trivial
      | e₁ :: e₂ :: u =>
        rw [cpcolor1_H_cons]
        split
        · exact Ctree.union_proper _ _ _ (key _ _ (by simp)) (key _ _ (by simp))
        · exact key _ _ (by simp)
    | A =>
      rw [foldHeight]
      match u with
      | [] => trivial
      | [_] => trivial
      | e₁ :: e₂ :: u =>
        rw [cpcolor1_A_cons]
        by_cases hee : e₁ = e₂
        · rw [ite_eq_left hee]
          cases u with
          | nil => exact key [e₁, e₂] _ (by simp)
          | cons x u => exact key (x :: u) _ (by simp)
        · rw [ite_eq_right hee]; trivial

/-! ### One step of the fold -/

/-- One construction step of the colouring fold is the union of the branches
enumerated by `enum1`.

The hypothesis on `f` records that `f` sends traces of equal length to trees of
equal height; the unions in `cpcolor1` are unions of such trees, and
`Ctree.mem_union` needs exactly that.  `proper_foldr` supplies it with
`h := foldHeight cp` for every `f` the fold actually uses. -/
theorem mem_cpcolor1 (s : CpStep) (f : List Color → Ctree) {h : ℕ → ℕ}
    (hf : ∀ u : List Color, Ctree.Proper (h u.length) (f u)) (et x : List Color) :
    Ctree.mem (cpcolor1 s f et) x = true ↔ ∃ t ∈ enum1 s et, Ctree.mem (f t) x = true := by
  have key : ∀ (v : List Color) (m : ℕ), v.length = m → Ctree.Proper (h m) (f v) := by
    intro v m hm; rw [← hm]; exact hf v
  cases s with
  | R n => simp
  | R' =>
    rw [cpcolor1_R', enum1_R']
    split <;> simp
  | U =>
    rw [cpcolor1_U, enum1_U,
      Ctree.mem_union _ _ _ _ (key _ _ (by simp))
        (Ctree.union_proper _ _ _ (key _ (et.length + 1 + 1) (by simp))
          (key _ (et.length + 1 + 1) (by simp))),
      Ctree.mem_union _ _ _ _ (key _ (et.length + 1 + 1) (by simp))
        (key _ (et.length + 1 + 1) (by simp))]
    simp
  | Y =>
    cases et with
    | nil => simp
    | cons e₁ et =>
      rw [cpcolor1_Y_cons, enum1_Y_cons,
        Ctree.mem_union _ _ _ _ (key _ (et.length + 1 + 1) (by simp))
          (key _ (et.length + 1 + 1) (by simp))]
      simp
  | K =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et =>
      rw [cpcolor1_K_cons, enum1_K_cons]
      split <;> simp
  | H =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et =>
      rw [cpcolor1_H_cons, enum1_H_cons]
      split
      · rw [Ctree.mem_union _ _ _ _ (key _ (et.length + 1 + 1) (by simp))
          (key _ (et.length + 1 + 1) (by simp))]
        simp
      · simp
  | A =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: [] =>
      rw [cpcolor1_A_cons, enum1_A_cons]
      split <;> simp
    | e₁ :: e₂ :: y :: et =>
      rw [cpcolor1_A_cons, enum1_A_cons]
      split <;> simp

/-! ### The whole fold -/

/-- Apply the steps of `cp` in order (head first) to every trace of `ts`. -/
def foldList : CProg → List (List Color) → List (List Color)
  | [], ts => ts
  | s :: cp, ts => foldList cp (ts.flatMap (enum1 s))

@[simp] theorem foldList_nil (ts : List (List Color)) : foldList [] ts = ts := rfl

@[simp] theorem foldList_cons (s : CpStep) (cp : CProg) (ts : List (List Color)) :
    foldList (s :: cp) ts = foldList cp (ts.flatMap (enum1 s)) := rfl

/-- The fold of `cp` over a list of traces is the fold of `cpcolor1` over each
of them. -/
theorem mem_foldList : ∀ (cp : CProg) (ts : List (List Color)) (x : List Color),
    (∃ u ∈ ts, Ctree.mem (List.foldr cpcolor1 cpbranch cp u) x = true) ↔
      ∃ t ∈ foldList cp ts, Ctree.mem (cpbranch t) x = true := by
  intro cp
  induction cp with
  | nil => intro ts x; rfl
  | cons s cp ih =>
    intro ts x
    rw [foldList_cons, ← ih]
    constructor
    · rintro ⟨u, hu, hx⟩
      rw [List.foldr_cons, mem_cpcolor1 s _ (proper_foldr cp)] at hx
      obtain ⟨t, ht, hxt⟩ := hx
      exact ⟨t, List.mem_flatMap.mpr ⟨u, hu, ht⟩, hxt⟩
    · rintro ⟨t, ht, hxt⟩
      obtain ⟨u, hu, htu⟩ := List.mem_flatMap.mp ht
      refine ⟨u, hu, ?_⟩
      rw [List.foldr_cons, mem_cpcolor1 s _ (proper_foldr cp)]
      exact ⟨t, htu, hxt⟩

/-- The fold of `cpcolor1` is the union of the branches of `foldList`. -/
theorem mem_foldr_cpcolor1 (cp : CProg) (et x : List Color) :
    Ctree.mem (List.foldr cpcolor1 cpbranch cp et) x = true ↔
      ∃ t ∈ foldList cp [et], Ctree.mem (cpbranch t) x = true := by
  rw [← mem_foldList cp [et] x]
  simp

/-! ### The outermost steps -/

/-- The final traces `cpcolor0 cp` folds over, including its symmetry special
cases. -/
def finalTraces : CProg → List (List Color)
  | .R _ :: cp => finalTraces cp
  | .Y :: cp => foldList cp [[c1, c2, c3]]
  | .U :: cp => foldList cp [[c1, c1, c2, c2]] ++ foldList cp [[c1, c1, c1, c1]]
  | cp => foldList cp [[c1, c1]]

/-- `cpcolor0 cp` is the union of the branches of `finalTraces cp`. -/
theorem mem_cpcolor0 : ∀ (cp : CProg) (x : List Color),
    Ctree.mem (cpcolor0 cp) x = true ↔
      ∃ t ∈ finalTraces cp, Ctree.mem (cpbranch t) x = true
  | .R _ :: cp, x => by rw [cpcolor0, finalTraces]; exact mem_cpcolor0 cp x
  | .Y :: cp, x => by rw [cpcolor0, finalTraces]; exact mem_foldr_cpcolor1 cp _ x
  | .U :: cp, x => by
      rw [cpcolor0, finalTraces,
        Ctree.mem_union (foldHeight cp 4) _ _ _ (proper_foldr cp [c1, c1, c2, c2])
          (proper_foldr cp [c1, c1, c1, c1])]
      rw [Bool.or_eq_true, mem_foldr_cpcolor1, mem_foldr_cpcolor1]
      simp only [List.mem_append]
      constructor
      · rintro (⟨t, ht, hx⟩ | ⟨t, ht, hx⟩) <;> exact ⟨t, by tauto, hx⟩
      · rintro ⟨t, ht | ht, hx⟩
        · exact Or.inl ⟨t, ht, hx⟩
        · exact Or.inr ⟨t, ht, hx⟩
  | [], x => mem_foldr_cpcolor1 [] [c1, c1] x
  | .R' :: cp, x => mem_foldr_cpcolor1 (.R' :: cp) [c1, c1] x
  | .K :: cp, x => mem_foldr_cpcolor1 (.K :: cp) [c1, c1] x
  | .H :: cp, x => mem_foldr_cpcolor1 (.H :: cp) [c1, c1] x
  | .A :: cp, x => mem_foldr_cpcolor1 (.A :: cp) [c1, c1] x


/-! ### The invariants of the enumerated traces

Every enumerated trace sums to zero and avoids the colour `0`; together these
force every enumerated trace to have length at least two, which is what makes
the branch of `cpbranch` a genuine trace. -/

/-- One step preserves the vanishing of the sum. -/
theorem sum_enum1 (s : CpStep) (et : List Color) (h : et.sum = 0) :
    ∀ t ∈ enum1 s et, t.sum = 0 := by
  have hY : ∀ c : Color, e231 c + (e312 c + c) = 0 := by decide
  have hY' : ∀ c : Color, e312 c + (e231 c + c) = 0 := by decide
  cases s with
  | R n =>
    intro t ht
    simp only [enum1_R, List.mem_singleton] at ht
    subst ht
    rw [(List.rotate_perm et n).sum_eq]
    exact h
  | R' =>
    intro t ht
    rw [enum1_R'] at ht
    split at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst ht
      rw [(List.rotate_perm et _).sum_eq]
      exact h
  | U =>
    intro t ht
    simp only [enum1_U, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp [h]
  | Y =>
    cases et with
    | nil => simp
    | cons e₁ et' =>
      intro t ht
      rw [List.sum_cons] at h
      have he : e₁ = et'.sum := Color.add_eq_zero_iff.mp h
      simp only [enum1_Y_cons, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · rw [List.sum_cons, List.sum_cons, ← he]; exact hY e₁
      · rw [List.sum_cons, List.sum_cons, ← he]; exact hY' e₁
  | K =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [enum1_K_cons] at ht
      split at ht
      · simp at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        rw [List.sum_cons, List.sum_cons] at h
        rw [List.sum_cons, add_assoc]
        exact h
  | H =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [List.sum_cons, List.sum_cons] at h
      rw [enum1_H_cons] at ht
      split at ht
      · rename_i hee
        subst hee
        rw [← add_assoc, Color.add_self, zero_add] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;>
          rw [List.sum_cons, List.sum_cons, ← add_assoc, Color.add_self, zero_add] <;> exact h
      · simp only [List.mem_singleton] at ht
        subst ht
        rw [List.sum_cons, List.sum_cons, add_left_comm]
        exact h
  | A =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [List.sum_cons, List.sum_cons] at h
      rw [enum1_A_cons] at ht
      split at ht
      · rename_i hee
        subst hee
        rw [← add_assoc, Color.add_self, zero_add] at h
        simp only [List.mem_singleton] at ht
        subst ht
        cases et' with
        | nil => simp
        | cons y et2 => exact h
      · simp at ht

/-- One step preserves the absence of the colour `0`. -/
theorem zero_notMem_enum1 (s : CpStep) (et : List Color) (h : (0 : Color) ∉ et) :
    ∀ t ∈ enum1 s et, (0 : Color) ∉ t := by
  have hne : ∀ c : Color, c ≠ 0 → e231 c ≠ 0 ∧ e312 c ≠ 0 := by decide
  cases s with
  | R n =>
    intro t ht
    simp only [enum1_R, List.mem_singleton] at ht
    subst ht
    simpa using h
  | R' =>
    intro t ht
    rw [enum1_R'] at ht
    split at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst ht
      simpa using h
  | U =>
    intro t ht
    simp only [enum1_U, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      · simp only [List.mem_cons, not_or]
        exact ⟨by decide, by decide, h⟩
  | Y =>
    cases et with
    | nil => simp
    | cons e₁ et' =>
      intro t ht
      have he₁ : e₁ ≠ 0 := fun hc => h (by simp [hc])
      have het : (0 : Color) ∉ et' := fun hc => h (List.mem_cons_of_mem _ hc)
      simp only [enum1_Y_cons, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · simp only [List.mem_cons, not_or]
        exact ⟨fun hc => (hne e₁ he₁).1 hc.symm, fun hc => (hne e₁ he₁).2 hc.symm, het⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨fun hc => (hne e₁ he₁).2 hc.symm, fun hc => (hne e₁ he₁).1 hc.symm, het⟩
  | K =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      have het : (0 : Color) ∉ et' := fun hc => h (by simp [hc])
      rw [enum1_K_cons] at ht
      split at ht
      · simp at ht
      · rename_i hee
        simp only [List.mem_singleton] at ht
        subst ht
        simp only [List.mem_cons, not_or]
        exact ⟨fun hc => hee (Color.add_eq_zero_iff.mp hc.symm), het⟩
  | H =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      have he₁ : e₁ ≠ 0 := fun hc => h (by simp [hc])
      have he₂ : e₂ ≠ 0 := fun hc => h (by simp [hc])
      have het : (0 : Color) ∉ et' := fun hc => h (by simp [hc])
      rw [enum1_H_cons] at ht
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · simp only [List.mem_cons, not_or]
          exact ⟨fun hc => (hne e₁ he₁).1 hc.symm, fun hc => (hne e₁ he₁).1 hc.symm, het⟩
        · simp only [List.mem_cons, not_or]
          exact ⟨fun hc => (hne e₁ he₁).2 hc.symm, fun hc => (hne e₁ he₁).2 hc.symm, het⟩
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [List.mem_cons, not_or]
        exact ⟨fun hc => he₂ hc.symm, fun hc => he₁ hc.symm, het⟩
  | A =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      have he₁ : e₁ ≠ 0 := fun hc => h (by simp [hc])
      have he₂ : e₂ ≠ 0 := fun hc => h (by simp [hc])
      have het : (0 : Color) ∉ et' := fun hc => h (by simp [hc])
      rw [enum1_A_cons] at ht
      split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        cases et' with
        | nil =>
          simp only [List.mem_cons, List.not_mem_nil, not_or]
          exact ⟨fun hc => he₁ hc.symm, fun hc => he₂ hc.symm, not_false⟩
        | cons y et2 => exact het
      · simp at ht

/-- One step preserves the length bound, given the other two invariants. -/
theorem two_le_length_enum1 (s : CpStep) (et : List Color) (hsum : et.sum = 0)
    (h0 : (0 : Color) ∉ et) (hl : 2 ≤ et.length) : ∀ t ∈ enum1 s et, 2 ≤ t.length := by
  cases s with
  | R n =>
    intro t ht
    simp only [enum1_R, List.mem_singleton] at ht
    subst ht
    simpa using hl
  | R' =>
    intro t ht
    rw [enum1_R'] at ht
    split at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst ht
      simpa using hl
  | U =>
    intro t ht
    simp only [enum1_U, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp
  | Y =>
    cases et with
    | nil => simp
    | cons e₁ et' =>
      intro t ht
      simp only [enum1_Y_cons, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp
  | K =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [enum1_K_cons] at ht
      split at ht
      · simp at ht
      · rename_i hee
        simp only [List.mem_singleton] at ht
        subst ht
        cases et' with
        | nil => exact absurd (Color.add_eq_zero_iff.mp (by simpa using hsum)) hee
        | cons y et2 => simp
  | H =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [enum1_H_cons] at ht
      split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> simp
      · simp only [List.mem_singleton] at ht
        subst ht
        simp
  | A =>
    match et with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: et' =>
      intro t ht
      rw [enum1_A_cons] at ht
      split at ht
      · rename_i hee
        subst hee
        simp only [List.mem_singleton] at ht
        subst ht
        cases et' with
        | nil => simp
        | cons y et2 =>
          cases et2 with
          | nil =>
            have hy : y = 0 := by
              have hs : e₁ + (e₁ + (y + 0)) = 0 := by simpa using hsum
              rw [← add_assoc, Color.add_self, zero_add, add_zero] at hs
              exact hs
            exact absurd (show (0 : Color) ∈ e₁ :: e₁ :: [y] by simp [hy]) h0
          | cons z et3 => simp
      · simp at ht

/-! ### Lifting the invariants to the fold -/

/-- `foldList` distributes over concatenation of the trace list. -/
theorem foldList_append : ∀ (cp : CProg) (ts₁ ts₂ : List (List Color)),
    foldList cp (ts₁ ++ ts₂) = foldList cp ts₁ ++ foldList cp ts₂
  | [], _, _ => rfl
  | s :: cp, ts₁, ts₂ => by
      rw [foldList_cons, List.flatMap_append, foldList_append cp, foldList_cons, foldList_cons]

/-- Every enumerated trace sums to zero when the input traces do. -/
theorem sum_foldList : ∀ (cp : CProg) (ts : List (List Color)),
    (∀ u ∈ ts, u.sum = 0) → ∀ t ∈ foldList cp ts, t.sum = 0
  | [], _, h => h
  | s :: cp, ts, h => by
      refine sum_foldList cp _ ?_
      intro u hu
      obtain ⟨v, hv, hvu⟩ := List.mem_flatMap.mp hu
      exact sum_enum1 s v (h v hv) u hvu

/-- Every enumerated trace avoids `0` when the input traces do. -/
theorem zero_notMem_foldList : ∀ (cp : CProg) (ts : List (List Color)),
    (∀ u ∈ ts, (0 : Color) ∉ u) → ∀ t ∈ foldList cp ts, (0 : Color) ∉ t
  | [], _, h => h
  | s :: cp, ts, h => by
      refine zero_notMem_foldList cp _ ?_
      intro u hu
      obtain ⟨v, hv, hvu⟩ := List.mem_flatMap.mp hu
      exact zero_notMem_enum1 s v (h v hv) u hvu

/-- Every enumerated trace has length at least two when the input traces satisfy
all three invariants. -/
theorem two_le_length_foldList : ∀ (cp : CProg) (ts : List (List Color)),
    (∀ u ∈ ts, u.sum = 0 ∧ (0 : Color) ∉ u ∧ 2 ≤ u.length) →
      ∀ t ∈ foldList cp ts, 2 ≤ t.length
  | [], _, h => fun t ht => (h t ht).2.2
  | s :: cp, ts, h => by
      refine two_le_length_foldList cp _ ?_
      intro u hu
      obtain ⟨v, hv, hvu⟩ := List.mem_flatMap.mp hu
      exact ⟨sum_enum1 s v (h v hv).1 u hvu, zero_notMem_enum1 s v (h v hv).2.1 u hvu,
        two_le_length_enum1 s v (h v hv).1 (h v hv).2.1 (h v hv).2.2 u hvu⟩

/-- `finalTraces` is a `foldList` of starting traces that sum to zero, avoid `0`
and have length at least two. -/
theorem exists_foldList_finalTraces : ∀ cp : CProg,
    ∃ (cp' : CProg) (ts : List (List Color)), finalTraces cp = foldList cp' ts ∧
      ∀ u ∈ ts, u.sum = 0 ∧ (0 : Color) ∉ u ∧ 2 ≤ u.length
  | .R _ :: cp => exists_foldList_finalTraces cp
  | .Y :: cp => ⟨cp, [[c1, c2, c3]], rfl, by decide⟩
  | .U :: cp =>
      ⟨cp, [[c1, c1, c2, c2], [c1, c1, c1, c1]], (foldList_append cp _ _).symm, by decide⟩
  | [] => ⟨[], [[c1, c1]], rfl, by decide⟩
  | .R' :: cp => ⟨.R' :: cp, [[c1, c1]], rfl, by decide⟩
  | .K :: cp => ⟨.K :: cp, [[c1, c1]], rfl, by decide⟩
  | .H :: cp => ⟨.H :: cp, [[c1, c1]], rfl, by decide⟩
  | .A :: cp => ⟨.A :: cp, [[c1, c1]], rfl, by decide⟩

/-- Every final trace sums to zero. -/
theorem sum_finalTraces (cp : CProg) : ∀ t ∈ finalTraces cp, t.sum = 0 := by
  obtain ⟨cp', ts, he, hts⟩ := exists_foldList_finalTraces cp
  rw [he]
  exact sum_foldList cp' ts fun u hu => (hts u hu).1

/-- No final trace contains the colour `0`. -/
theorem zero_notMem_finalTraces (cp : CProg) : ∀ t ∈ finalTraces cp, (0 : Color) ∉ t := by
  obtain ⟨cp', ts, he, hts⟩ := exists_foldList_finalTraces cp
  rw [he]
  exact zero_notMem_foldList cp' ts fun u hu => (hts u hu).2.1

/-- Every final trace has length at least two. -/
theorem two_le_length_finalTraces (cp : CProg) : ∀ t ∈ finalTraces cp, 2 ≤ t.length := by
  obtain ⟨cp', ts, he, hts⟩ := exists_foldList_finalTraces cp
  rw [he]
  exact two_le_length_foldList cp' ts hts

/-! ### The colouring tree as a fold -/

/-- The canonical form of a proper trace, with the normalisation done in one
pass. -/
theorem evenNormTail_cons {a : Color} (ha : a ≠ 0) (u : List Color) :
    evenNormTail (a :: u) = u.map (evenPerm (a :: u) * rotTo a) := by
  rw [evenNormTail, normTail, ite_eq_right ha, map_map_edgePerm]

/-- The branch of a trace that avoids `0` and has length at least two contains
exactly the canonical form of its tail. -/
theorem mem_cpbranch_iff {t : List Color} (h0 : (0 : Color) ∉ t) (hl : 2 ≤ t.length)
    (y : List Color) : Ctree.mem (cpbranch t) y = true ↔ y = evenNormTail t.tail := by
  obtain ⟨c, a, u, rfl⟩ : ∃ c a u, t = c :: a :: u := by
    cases t with
    | nil => exact absurd hl (by simp)
    | cons c r =>
      cases r with
      | nil => exact absurd hl (by simp)
      | cons a u => exact ⟨c, a, u, rfl⟩
  have ha : a ≠ 0 := fun hc => h0 (by simp [hc])
  have hu : (0 : Color) ∉ u := fun hc => h0 (by simp [hc])
  have hz : (0 : Color) ∉ evenNormTail (c :: a :: u).tail := by
    rw [List.tail_cons, evenNormTail_cons ha]
    simpa using hu
  rw [cpbranch_spec]
  exact Ctree.mem_ofTrace _ hz y

/-- A trace whose normalised tail is the canonical form of `u` is an edge
permutation of `u`. -/
theorem exists_map_of_normTail_eq {u v : List Color} (hu : (0 : Color) ∉ u) (hne : u ≠ [])
    (hx : normTail v = evenNormTail u) : ∃ g : EdgePerm, v = u.map g := by
  cases u with
  | nil => exact absurd rfl hne
  | cons a u =>
    have ha : a ≠ 0 := fun hc => hu (by simp [hc])
    have hu' : (0 : Color) ∉ u := fun hc => hu (by simp [hc])
    have heven : evenNormTail (a :: u) = u.map (evenPerm (a :: u) * rotTo a) :=
      evenNormTail_cons ha u
    have hz : (0 : Color) ∉ evenNormTail (a :: u) := by rw [heven]; simpa using hu'
    cases v with
    | nil =>
      exact absurd (hx ▸ (by simp [normTail] : (0 : Color) ∈ normTail ([] : List Color))) hz
    | cons d v =>
      by_cases hd : d = 0
      · subst hd
        exact absurd (hx ▸ (by simp [normTail] : (0 : Color) ∈ normTail ((0 : Color) :: v))) hz
      · have hnv : normTail (d :: v) = v.map (rotTo d) := by rw [normTail, ite_eq_right hd]
        refine ⟨(rotTo d)⁻¹ * (evenPerm (a :: u) * rotTo a), ?_⟩
        rw [List.map_cons]
        congr 1
        · rw [mul_apply, mul_apply, rotTo_apply_self ha, evenPerm_eq_evenTailPerm,
            evenTailPerm_apply_c1, ← rotTo_apply_self hd, inv_apply_apply]
        · rw [← map_map_edgePerm, ← heven, ← hx, hnv, map_map_edgePerm, inv_mul_cancel,
            map_one_edgePerm]

/-- **The specification of the colouring tree as a fold.**  The traces of
`cpcolor cp` are exactly the even traces that are edge permutations of the tail
of one of the traces the program enumerates. -/
theorem mem_cpcolor_iff (cp : CProg) (v : List Color) :
    Ctree.mem (cpcolor cp) v = true ↔
      evenTrace v = true ∧ ∃ t ∈ finalTraces cp.reverse, ∃ g : EdgePerm, v = t.tail.map g := by
  rw [cpcolor, Ctree.mem_consRot, mem_cpcolor0]
  constructor
  · rintro ⟨t, ht, hx⟩
    have h0 := zero_notMem_finalTraces _ t ht
    have hl := two_le_length_finalTraces _ t ht
    rw [mem_cpbranch_iff h0 hl] at hx
    have hev : evenTrace v = true := by rw [evenTrace, hx]; exact evenTail_evenNormTail _
    refine ⟨hev, t, ht, exists_map_of_normTail_eq (fun hc => h0 (List.mem_of_mem_tail hc))
      (fun hc => ?_) hx⟩
    have hlen : t.tail.length = 0 := by rw [hc]; rfl
    rw [List.length_tail] at hlen
    omega
  · rintro ⟨hev, t, ht, g, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [mem_cpbranch_iff (zero_notMem_finalTraces _ t ht) (two_le_length_finalTraces _ t ht)]
    have h1 : evenPerm (t.tail.map g) = 1 := by rw [evenPerm, ite_eq_left hev]
    have h2 : evenNormTail (t.tail.map g) = normTail (t.tail.map g) := by
      rw [evenNormTail, h1, map_one_edgePerm]
    rw [← h2, evenNormTail_map]

end Bulk
end FourColor

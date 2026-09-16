import FourColor.Perm
import FourColor.Path
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Orbits as lists

The orbit of a dart under one of the three permutations of a hypermap, listed
in order from that dart: `[x, f x, f² x, …]`, stopping just before it returns.
This is the reference's `orbit`, and its length is the reference's `order` —
for the `face` permutation, the *arity* of a face.

## Main definitions

* `orbitList f x` — the orbit of `x` under `f`, as a duplicate-free list.

## Main results

* `mem_orbitList` — its members are exactly the darts on the orbit.
* `nodup_orbitList`, `isChain_orbitList`, `apply_getLastD_orbitList` — it is
  duplicate-free, each dart is the image of the previous one, and it closes up
  into a cycle.
-/

namespace FourColor

open Equiv Equiv.Perm Function

variable {D : Type*}

/-- The orbit of `x` under `f`, listed in order from `x`. -/
noncomputable def orbitList (f : Perm D) (x : D) : List D :=
  (List.range (minimalPeriod f x)).map fun n => (f ^ n) x

@[simp] theorem length_orbitList (f : Perm D) (x : D) :
    (orbitList f x).length = minimalPeriod f x := by
  simp [orbitList]

theorem isPeriodicPt_orderOf [Finite D] (f : Perm D) (x : D) :
    IsPeriodicPt f (orderOf f) x := by
  show f^[orderOf f] x = x
  rw [Perm.iterate_eq_pow, pow_orderOf_eq_one]
  rfl

theorem minimalPeriod_pos [Finite D] (f : Perm D) (x : D) : 0 < minimalPeriod f x :=
  (isPeriodicPt_orderOf f x).minimalPeriod_pos (orderOf_pos f)

theorem orbitList_ne_nil [Finite D] (f : Perm D) (x : D) : orbitList f x ≠ [] := by
  intro h
  have := length_orbitList f x
  rw [h, List.length_nil] at this
  exact absurd this.symm (minimalPeriod_pos f x).ne'

theorem pow_minimalPeriod (f : Perm D) (x : D) : (f ^ minimalPeriod f x) x = x := by
  have h := isPeriodicPt_minimalPeriod f x
  rwa [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow] at h

theorem mem_orbitList [Finite D] {f : Perm D} {x y : D} :
    y ∈ orbitList f x ↔ f.SameCycle x y := by
  constructor
  · rintro hy
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp hy
    exact ⟨n, by simp⟩
  · intro h
    rw [sameCycle_iff_reflTransGen] at h
    obtain ⟨n, hn⟩ := exists_pow_of_reflTransGen h
    refine List.mem_map.mpr ⟨n % minimalPeriod f x, ?_, ?_⟩
    · exact List.mem_range.mpr (Nat.mod_lt _ (minimalPeriod_pos f x))
    · have := iterate_mod_minimalPeriod_eq (f := (f : D → D)) (x := x) (n := n)
      rw [Perm.iterate_eq_pow, Perm.iterate_eq_pow] at this
      rw [this, hn]

theorem nodup_orbitList (f : Perm D) (x : D) : (orbitList f x).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  refine iterate_injOn_Iio_minimalPeriod (f := (f : D → D)) (x := x)
    (List.mem_range.mp hi) (List.mem_range.mp hj) ?_
  simpa [Perm.iterate_eq_pow] using hij

/-- A list of iterates is a chain under the map. -/
theorem isChain_map_range (f : Perm D) : ∀ (n : ℕ) (g : ℕ → D),
    (∀ i, g (i + 1) = f (g i)) →
      List.IsChain (fun a b => b = f a) ((List.range n).map g) := by
  intro n
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.isChain_cons.mpr ⟨?_, ih (g ∘ Nat.succ) fun i => hg (i + 1)⟩
    intro b hb
    match n with
    | 0 => simp at hb
    | m + 1 =>
      rw [List.range_succ_eq_map, List.map_cons] at hb
      rw [List.head?_cons, Option.mem_def, Option.some_inj] at hb
      rw [← hb]
      exact hg 0

theorem isChain_orbitList (f : Perm D) (x : D) :
    List.IsChain (fun a b => b = f a) (orbitList f x) :=
  isChain_map_range f _ _ fun i => by rw [pow_succ']; rfl

theorem head_orbitList [Finite D] (f : Perm D) (x : D) :
    (orbitList f x).headD x = x := by
  have hpos := minimalPeriod_pos f x
  match h : minimalPeriod f x with
  | 0 => exact absurd h hpos.ne'
  | m + 1 => simp [orbitList, h, List.range_succ_eq_map]

/-- The orbit closes up: the image of its last dart is the dart it started
from. -/
theorem apply_getLastD_orbitList [Finite D] (f : Perm D) (x : D) :
    f ((orbitList f x).getLastD x) = x := by
  have hpos := minimalPeriod_pos f x
  match h : minimalPeriod f x with
  | 0 => exact absurd h hpos.ne'
  | m + 1 =>
    have hlast : (orbitList f x).getLastD x = (f ^ m) x := by
      have : orbitList f x = (List.range (m + 1)).map fun n => (f ^ n) x := by
        rw [orbitList, h]
      rw [this, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        getLastD_append_cons]
      rfl
    have hp : (f ^ (m + 1)) x = x := by
      have hpm := pow_minimalPeriod f x
      rwa [h] at hpm
    rw [hlast, ← Perm.mul_apply, ← pow_succ']
    exact hp

end FourColor

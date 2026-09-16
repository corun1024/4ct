import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Logic.Relation
import FourColor.Adjoin

/-!
# Permutations: orbit counting and point deletion

Two pieces of permutation theory used throughout the Four Colour Theorem
development.

The first is `cycleCount`, the number of orbits of a permutation, which is what
the Euler formula for hypermaps counts.  It is invariant under inversion and
conjugation, which is all that is needed to see that the derived hypermaps have
the same genus.

The second is `skip f z`, the permutation of `{x // x ≠ z}` obtained by deleting
`z` from its cycle.  This is the engine of the Walkup construction: the cycle
representation of `skip f z` is that of `f` with `z` removed, so deleting a dart
costs exactly one orbit when `z` was a fixed point and none otherwise
(`cycleCount_skip`).

On a finite type `SameCycle` coincides with forward reachability
(`sameCycle_iff_reflTransGen`), which is the form in which the cycle structure of
`skip` is easiest to analyse.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D D' : Type*}

/-! ### Orbits as forward reachability -/

/-- Forward steps of a permutation reach all of its powers. -/
theorem reflTransGen_perm_pow (f : Perm D) (n : ℕ) (x : D) :
    Relation.ReflTransGen (fun a b => b = f a) x ((f ^ n) x) := by
  induction n with
  | zero => simpa using Relation.ReflTransGen.refl (r := fun a b => b = f a) (a := x)
  | succ n ih =>
    refine ih.tail ?_
    rw [pow_succ']
    rfl

/-- On a finite type the inverse image of a dart is reachable by *forward*
steps, because a permutation has finite order. -/
theorem reflTransGen_perm_inv [Finite D] (f : Perm D) (x : D) :
    Relation.ReflTransGen (fun a b => b = f a) x (f⁻¹ x) := by
  have hpos : 0 < orderOf f := orderOf_pos f
  have hmul : f ^ (orderOf f - 1) * f = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have h : f ^ (orderOf f - 1) = f⁻¹ := eq_inv_of_mul_eq_one_left hmul
  simpa [h] using reflTransGen_perm_pow f (orderOf f - 1) x

/-- Forward steps of a permutation reach all powers of its inverse, since each
inverse step is itself a forward path. -/
theorem reflTransGen_perm_inv_pow [Finite D] (f : Perm D) (n : ℕ) (x : D) :
    Relation.ReflTransGen (fun a b => b = f a) x ((f⁻¹ ^ n) x) := by
  induction n with
  | zero => simpa using Relation.ReflTransGen.refl (r := fun a b => b = f a) (a := x)
  | succ n ih =>
    refine ih.trans ?_
    rw [pow_succ', Perm.mul_apply]
    exact reflTransGen_perm_inv f _

/-- On a finite type, lying on a common orbit is the same as forward
reachability. -/
theorem sameCycle_iff_reflTransGen [Finite D] (f : Perm D) (x y : D) :
    f.SameCycle x y ↔ Relation.ReflTransGen (fun a b => b = f a) x y := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : 0 ≤ i
    · lift i to ℕ using hi with n
      simpa using reflTransGen_perm_pow f n x
    · have hnat : ((i.natAbs : ℤ)) = -i := by omega
      have he : (f⁻¹ ^ i.natAbs) x = (f ^ i) x := by
        rw [inv_pow, ← zpow_natCast, hnat, zpow_neg, inv_inv]
      rw [← he]
      exact reflTransGen_perm_inv_pow f _ x
  · intro h
    induction h with
    | refl => exact SameCycle.refl f x
    | tail _ hb ih => exact hb ▸ ih.trans ⟨1, by simp⟩


/-- Forward reachability is realised by some power of the permutation. -/
theorem exists_pow_of_reflTransGen {f : Perm D} {x y : D}
    (h : Relation.ReflTransGen (fun a b => b = f a) x y) : ∃ n : ℕ, (f ^ n) x = y := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [pow_succ', Perm.mul_apply, hn, hbc]⟩


/-! ### Counting orbits -/

/-- The number of orbits of a permutation. -/
noncomputable def cycleCount (f : Perm D) : ℕ := Nat.card (Quotient (SameCycle.setoid f))

theorem cycleCount_congr (e : D ≃ D') {f : Perm D} {f' : Perm D'}
    (h : ∀ x y, f.SameCycle x y ↔ f'.SameCycle (e x) (e y)) :
    cycleCount f = cycleCount f' :=
  Nat.card_congr (Quotient.congr e h)

@[simp] theorem cycleCount_inv (f : Perm D) : cycleCount f⁻¹ = cycleCount f :=
  cycleCount_congr (Equiv.refl D) fun x y => by simp [sameCycle_inv]

theorem cycleCount_conj (g f : Perm D) : cycleCount (g * f * g⁻¹) = cycleCount f :=
  (cycleCount_congr (f := f) (f' := g * f * g⁻¹) g fun x y => by
    refine ⟨fun h => h.conj, fun h => ?_⟩
    have h' := h.conj (g := g⁻¹)
    simpa [mul_assoc] using h').symm

theorem cycleCount_mul_comm (f g : Perm D) : cycleCount (f * g) = cycleCount (g * f) := by
  have h : g * (f * g) * g⁻¹ = g * f := by simp [mul_assoc]
  rw [← cycleCount_conj g (f * g), h]

/-! ### Deleting a point from a permutation -/

variable [DecidableEq D]

/-- The underlying map of `skip`: step by `f`, but step over `z`. -/
def skipFun (f : Perm D) (z x : D) : D := if f x = z then f z else f x

theorem skipFun_ne (f : Perm D) (z : D) {x : D} (hx : x ≠ z) : skipFun f z x ≠ z := by
  unfold skipFun
  split
  · rename_i h
    exact fun hz => hx (f.injective (h.trans hz.symm))
  · rename_i h
    exact h

theorem skipFun_inv (f : Perm D) (z : D) {x : D} (hx : x ≠ z) :
    skipFun f⁻¹ z (skipFun f z x) = x := by
  by_cases h : f x = z
  · have hzx : f⁻¹ z = x := by rw [← h]; simp
    simp [skipFun, h, hzx]
  · simp [skipFun, h, hx]

/-- `skip f z` is the permutation of `{x // x ≠ z}` obtained from `f` by deleting
`z` from its cycle: where `f` would step onto `z`, `skip f z` steps over it. -/
def skip (f : Perm D) (z : D) : Perm {x : D // x ≠ z} where
  toFun u := ⟨skipFun f z u.val, skipFun_ne f z u.2⟩
  invFun u := ⟨skipFun f⁻¹ z u.val, skipFun_ne f⁻¹ z u.2⟩
  left_inv u := Subtype.ext (skipFun_inv f z u.2)
  right_inv u := Subtype.ext (by
    have := skipFun_inv f⁻¹ z u.2
    rwa [inv_inv] at this)

@[simp] theorem skip_val (f : Perm D) (z : D) (u : {x : D // x ≠ z}) :
    (skip f z u).val = skipFun f z u.val := rfl

theorem skip_val_of_ne {f : Perm D} {z : D} {u : {x : D // x ≠ z}} (h : f u.val ≠ z) :
    (skip f z u).val = f u.val := by simp [skipFun, h]

theorem skip_val_of_eq {f : Perm D} {z : D} {u : {x : D // x ≠ z}} (h : f u.val = z) :
    (skip f z u).val = f z := by simp [skipFun, h]

private theorem reflTransGen_skip_of_pow [Finite D] (f : Perm D) (z : D) (n : ℕ) :
    ∀ (u v : {x : D // x ≠ z}), (f ^ n) u.val = v.val →
      Relation.ReflTransGen (fun a b => b = skip f z a) u v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hn
    match n with
    | 0 =>
      have : u = v := Subtype.ext (by simpa using hn)
      exact this ▸ Relation.ReflTransGen.refl
    | (m + 1) =>
      by_cases hu : f u.val = z
      · have hfz : f z ≠ z := fun hz => u.2 (f.injective (hu.trans hz.symm))
        match m with
        | 0 =>
          rw [pow_succ, Perm.mul_apply, hu] at hn
          exact absurd (by simpa using hn.symm) v.2
        | (k + 1) =>
          have hstep : (f ^ k) (f z) = v.val := by
            rw [pow_succ, Perm.mul_apply, hu, pow_succ, Perm.mul_apply] at hn
            exact hn
          refine Relation.ReflTransGen.head (b := ⟨f z, hfz⟩) ?_
            (ih k (by omega) ⟨f z, hfz⟩ v hstep)
          exact Subtype.ext (skip_val_of_eq hu).symm
      · have hstep : (f ^ m) (f u.val) = v.val := by
          rw [pow_succ, Perm.mul_apply] at hn
          exact hn
        refine Relation.ReflTransGen.head (b := ⟨f u.val, hu⟩) ?_
          (ih m (by omega) ⟨f u.val, hu⟩ v hstep)
        exact Subtype.ext (skip_val_of_ne hu).symm

/-- Deleting a point does not change which darts lie on a common orbit. -/
theorem sameCycle_skip [Finite D] (f : Perm D) (z : D) (u v : {x : D // x ≠ z}) :
    (skip f z).SameCycle u v ↔ f.SameCycle u.val v.val := by
  rw [sameCycle_iff_reflTransGen, sameCycle_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine ih.trans ?_
      subst hbc
      by_cases hb : f b.val = z
      · rw [skip_val_of_eq hb]
        exact Relation.ReflTransGen.head (b := z) hb.symm (Relation.ReflTransGen.single rfl)
      · rw [skip_val_of_ne hb]
        exact Relation.ReflTransGen.single rfl
  · intro h
    obtain ⟨n, hn⟩ := exists_pow_of_reflTransGen h
    exact reflTransGen_skip_of_pow f z n u v hn

end FourColor

namespace FourColor

open Equiv Equiv.Perm

variable {D : Type*} [DecidableEq D]

/-! ### The orbit count of a deleted permutation -/

/-- The orbit of a dart `u ≠ z` under `skip f z`, viewed as an orbit under `f`. -/
private def skipQuot (f : Perm D) (z : D) [Finite D] :
    Quotient (SameCycle.setoid (skip f z)) → Quotient (SameCycle.setoid f) :=
  Quotient.lift (fun u => Quotient.mk (SameCycle.setoid f) u.val)
    (fun _ _ h => Quotient.sound ((sameCycle_skip f z _ _).mp h))

private theorem skipQuot_injective [Finite D] (f : Perm D) (z : D) :
    Function.Injective (skipQuot f z) := fun a b =>
  Quotient.inductionOn₂ a b fun u v hab =>
    Quotient.sound ((sameCycle_skip f z u v).mpr (Quotient.exact hab))

/-- Deleting a dart that is **not** a fixed point leaves the number of orbits
unchanged: its orbit merely gets one element shorter. -/
theorem cycleCount_skip_of_ne [Finite D] {f : Perm D} {z : D} (hz : f z ≠ z) :
    cycleCount (skip f z) = cycleCount f := by
  refine Nat.card_eq_of_bijective (skipQuot f z) ⟨skipQuot_injective f z, ?_⟩
  refine Quotient.ind fun x => ?_
  by_cases hx : x = z
  · refine ⟨Quotient.mk _ ⟨f z, hz⟩, ?_⟩
    subst hx
    exact Quotient.sound ⟨-1, by simp⟩
  · exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

/-- Deleting a fixed point removes exactly one orbit. -/
theorem cycleCount_skip_of_eq [Finite D] {f : Perm D} {z : D} (hz : f z = z) :
    cycleCount f = 1 + cycleCount (skip f z) := by
  have hfix : ∀ x : D, f.SameCycle x z → x = z := fun _ h => h.eq_of_right hz
  have hbij : Function.Bijective
      (fun o : Option (Quotient (SameCycle.setoid (skip f z))) =>
        o.elim (Quotient.mk (SameCycle.setoid f) z) (skipQuot f z)) := by
    constructor
    · rintro (_ | a) (_ | b) hab
      · rfl
      · revert hab
        refine Quotient.inductionOn b fun v hab => ?_
        exact absurd (hfix v.val (Quotient.exact hab).symm) v.2
      · revert hab
        refine Quotient.inductionOn a fun u hab => ?_
        exact absurd (hfix u.val (Quotient.exact hab)) u.2
      · exact congrArg some (skipQuot_injective f z hab)
    · refine Quotient.ind fun x => ?_
      by_cases hx : x = z
      · exact ⟨none, by rw [hx]; rfl⟩
      · exact ⟨some (Quotient.mk _ ⟨x, hx⟩), rfl⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [Finite.card_option] at hcard
  simp only [cycleCount]
  omega

/-- Deleting a dart costs exactly one orbit when it was a fixed point, and none
otherwise.  This is what makes the Walkup construction change the Euler
characteristic in a controlled way. -/
theorem cycleCount_skip [Finite D] (f : Perm D) (z : D) :
    cycleCount f = (if f z = z then 1 else 0) + cycleCount (skip f z) := by
  by_cases hz : f z = z
  · rw [ite_eq_left hz]; exact cycleCount_skip_of_eq hz
  · rw [ite_eq_right hz, Nat.zero_add, cycleCount_skip_of_ne hz]

/-! ### Orbit count via cycle structure

The number of orbits of a permutation is the number of its fixed points plus the
number of its nontrivial cycles.  Combined with `Equiv.Perm.sign_of_cycleType`
this pins down the parity of `cycleCount`, which is what the Euler formula for
hypermaps needs — and it replaces the reference's use of the full Walkup
induction to obtain that parity.
-/

section OrbitCount

open Equiv.Perm Function

variable {D : Type*} [DecidableEq D] [Fintype D]

/-- The orbits of a permutation are its fixed points together with its
nontrivial cycles. -/
theorem cycleCount_eq (f : Perm D) :
    cycleCount f = Nat.card (fixedPoints f) + f.cycleFactorsFinset.card := by
  classical
  have hmem : ∀ x : D, ¬ f x = x → f.cycleOf x ∈ f.cycleFactorsFinset := fun x hx =>
    cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)
  let T := (fixedPoints f ⊕ {c : Perm D // c ∈ f.cycleFactorsFinset})
  let g : D → T := fun x =>
    if hx : f x = x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨f.cycleOf x, hmem x hx⟩
  have hwd : ∀ x y : D, (SameCycle.setoid f).r x y → g x = g y := by
    intro x y h0
    have h : SameCycle f x y := h0
    by_cases hx : f x = x
    · have hy : f y = y := (h.apply_eq_self_iff).mp hx
      have hxy : x = y := h.eq_of_left hx
      subst hxy
      simp only [g]
    · have hy : ¬ f y = y := fun hc => hx ((h.apply_eq_self_iff).mpr hc)
      simp only [g, dite_eq_right hx, dite_eq_right hy]
      exact congrArg Sum.inr (Subtype.ext h.cycleOf_eq)
  have hbij : Function.Bijective (@Quotient.lift D T (SameCycle.setoid f) g hwd) := by
    constructor
    · refine fun a b => Quotient.inductionOn₂ a b fun x y hxy => ?_
      simp only [Quotient.lift_mk] at hxy
      refine Quotient.sound ?_
      by_cases hx : f x = x
      · by_cases hy : f y = y
        · simp only [g, dite_eq_right, dite_eq_left hx, dite_eq_left hy] at hxy
          have hxy' : x = y := congrArg Subtype.val (Sum.inl_injective hxy)
          subst hxy'
          exact SameCycle.refl f x
        · simp only [g, dite_eq_left hx, dite_eq_right hy] at hxy
          simp at hxy
      · by_cases hy : f y = y
        · simp only [g, dite_eq_right hx, dite_eq_left hy] at hxy
          simp at hxy
        · simp only [g, dite_eq_right hx, dite_eq_right hy] at hxy
          have hxy' : f.cycleOf x = f.cycleOf y :=
            congrArg Subtype.val (Sum.inr_injective hxy)
          exact (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr hx)
            (mem_support.mpr hy)).mpr hxy'
    · rintro (⟨x, hx⟩ | ⟨c, hc⟩)
      · have hx' : f x = x := hx
        exact ⟨Quotient.mk (SameCycle.setoid f) x, by
          simp only [Quotient.lift_mk, g, dite_eq_left hx']⟩
      · obtain ⟨a, ha⟩ : c.support.Nonempty :=
          (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
        have hfa : ¬ f a = a := mem_support.mp (mem_cycleFactorsFinset_support_le hc ha)
        refine ⟨Quotient.mk (SameCycle.setoid f) a, ?_⟩
        simp only [Quotient.lift_mk, g, dite_eq_right hfa]
        exact congrArg Sum.inr (Subtype.ext (cycle_is_cycleOf ha hc).symm)
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [cycleCount, hcard]
  simp only [T, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe]

theorem card_cycleFactorsFinset (f : Perm D) :
    f.cycleFactorsFinset.card = Multiset.card f.cycleType := by
  simp [Equiv.Perm.cycleType]

theorem cycleCount_eq' (f : Perm D) :
    cycleCount f = (Fintype.card D - f.cycleType.sum) + Multiset.card f.cycleType := by
  rw [cycleCount_eq, card_cycleFactorsFinset, Nat.card_eq_fintype_card, card_fixedPoints]

/-- The parity of the number of orbits of a permutation is determined by its
sign. -/
theorem neg_one_pow_cycleCount (f : Perm D) :
    (-1 : ℤˣ) ^ cycleCount f = (-1 : ℤˣ) ^ Fintype.card D * sign f := by
  rw [cycleCount_eq', sign_of_cycleType, ← pow_add]
  have hle : f.cycleType.sum ≤ Fintype.card D := sum_cycleType_le f
  have hmod : (Fintype.card D - f.cycleType.sum + Multiset.card f.cycleType) % 2
      = (Fintype.card D + (f.cycleType.sum + Multiset.card f.cycleType)) % 2 := by omega
  rcases Nat.even_or_odd (Fintype.card D - f.cycleType.sum + Multiset.card f.cycleType) with
    h | h
  · have hb : Even (Fintype.card D + (f.cycleType.sum + Multiset.card f.cycleType)) :=
      Nat.even_iff.mpr (by rw [← hmod]; exact Nat.even_iff.mp h)
    rw [h.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd (Fintype.card D + (f.cycleType.sum + Multiset.card f.cycleType)) :=
      Nat.odd_iff.mpr (by rw [← hmod]; exact Nat.odd_iff.mp h)
    rw [h.neg_one_pow, hb.neg_one_pow]

end OrbitCount

/-! ### Multiplying by a transposition

Multiplying a permutation by a transposition changes its number of orbits by
exactly one: down when the two transposed points lay on different orbits (the
orbits merge), up when they lay on the same one (the orbit splits).  This is the
single atomic counting fact the Euler formula for hypermaps rests on, since the
Walkup construction changes one of the three permutations by a transposition.

Merging is `Setoid.adjoin`: the orbits of `swap a b * g` and of `g` become the
same equivalence once the classes of `a` and `b` are merged, so the two orbit
counts differ by at most one.  Which way round is then settled by parity, via
`neg_one_pow_cycleCount` and `sign (swap a b * g) = -sign g`, with no need for
the combinatorial split-or-merge dichotomy.
-/

section Transposition

open Equiv Equiv.Perm

variable {D : Type*} [DecidableEq D] [Fintype D]

omit [Fintype D] in
/-- One step of `swap a b * g` stays inside the orbits of `g` with the classes
of `a` and `b` merged. -/
theorem adjoin_sameCycle_step (g : Perm D) (a b u : D) :
    (Setoid.adjoin (SameCycle.setoid g) a b) u ((swap a b * g) u) := by
  have hstep : g.SameCycle u (g u) := ⟨1, by simp⟩
  rcases eq_or_ne (g u) a with h | ha
  · have h1 : g.SameCycle u a := by rw [← h]; exact hstep
    have h2 : (swap a b * g) u = b := by rw [Perm.mul_apply, h, swap_apply_left]
    exact Or.inr (Or.inl ⟨h1, by rw [h2]⟩)
  · rcases eq_or_ne (g u) b with h | hb
    · have h1 : g.SameCycle u b := by rw [← h]; exact hstep
      have h2 : (swap a b * g) u = a := by rw [Perm.mul_apply, h, swap_apply_right]
      exact Or.inr (Or.inr ⟨h1, by rw [h2]⟩)
    · have h2 : (swap a b * g) u = g u := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne ha hb]
      exact Or.inl (by rw [h2]; exact hstep)

/-- The orbits of `swap a b * g` are contained in the orbits of `g` with the
classes of `a` and `b` merged. -/
theorem sameCycle_swap_mul_le_adjoin (g : Perm D) (a b : D) {x y : D}
    (h : (swap a b * g).SameCycle x y) :
    (Setoid.adjoin (SameCycle.setoid g) a b) x y := by
  rw [sameCycle_iff_reflTransGen] at h
  induction h with
  | refl => exact (Setoid.adjoin (SameCycle.setoid g) a b).refl' x
  | @tail v w _ hvw ih =>
    refine (Setoid.adjoin (SameCycle.setoid g) a b).trans' ih ?_
    rw [hvw]
    exact adjoin_sameCycle_step g a b v

/-- Merging the classes of `a` and `b` makes the orbits of `g` and of
`swap a b * g` the same equivalence. -/
theorem adjoin_sameCycle_swap_mul (g : Perm D) (a b : D) :
    Setoid.adjoin (SameCycle.setoid (swap a b * g)) a b
      = Setoid.adjoin (SameCycle.setoid g) a b := by
  have hg : swap a b * (swap a b * g) = g := by
    rw [← mul_assoc, swap_mul_self, one_mul]
  refine Setoid.ext fun x y => ⟨?_, ?_⟩
  · exact Setoid.adjoin_le (fun _ _ h => sameCycle_swap_mul_le_adjoin g a b h)
      (Setoid.adjoin_rel _ a b)
  · refine Setoid.adjoin_le (fun u v h => ?_) (Setoid.adjoin_rel _ a b)
    exact sameCycle_swap_mul_le_adjoin (swap a b * g) a b (by rw [hg]; exact h)

omit [DecidableEq D] [Fintype D] in
theorem cycleCount_eq_card_adjoin_of_sameCycle {g : Perm D} {a b : D}
    (h : g.SameCycle a b) :
    cycleCount g = Nat.card (Quotient (Setoid.adjoin (SameCycle.setoid g) a b)) := by
  rw [cycleCount, Setoid.adjoin_eq_self_of h]

omit [DecidableEq D] in
theorem cycleCount_eq_card_adjoin_of_not {g : Perm D} {a b : D}
    (h : ¬ g.SameCycle a b) :
    cycleCount g
      = Nat.card (Quotient (Setoid.adjoin (SameCycle.setoid g) a b)) + 1 := by
  rw [cycleCount, ← Setoid.card_quotient_adjoin_of_not (r := SameCycle.setoid g) h]

theorem neg_one_pow_mod_two (m : ℕ) : (-1 : ℤˣ) ^ m = (-1 : ℤˣ) ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Multiplying by a transposition changes the parity of the number of
orbits. -/
theorem cycleCount_swap_mul_mod_two (g : Perm D) {a b : D} (hab : a ≠ b) :
    cycleCount (swap a b * g) % 2 ≠ cycleCount g % 2 := by
  intro hmod
  have h1 := neg_one_pow_cycleCount (swap a b * g)
  have h2 := neg_one_pow_cycleCount g
  rw [neg_one_pow_mod_two, hmod, ← neg_one_pow_mod_two, h2, sign_mul, sign_swap hab] at h1
  have h3 : (1 : ℤˣ) = -1 := by
    have h4 : Perm.sign g = -1 * Perm.sign g := mul_left_cancel h1
    exact mul_right_cancel (a := (1 : ℤˣ)) (b := Perm.sign g) (by rw [one_mul]; exact h4)
  have h5 : (1 : ℤ) = -1 := by simpa using congrArg Units.val h3
  omega

/-- Multiplying by a transposition either splits an orbit or merges two: the
two points lie on a common orbit of exactly one of `g` and `swap a b * g`. -/
theorem sameCycle_swap_mul_iff (g : Perm D) {a b : D} (hab : a ≠ b) :
    (swap a b * g).SameCycle a b ↔ ¬ g.SameCycle a b := by
  have hpar := cycleCount_swap_mul_mod_two g hab
  constructor
  · intro hs h
    rw [cycleCount_eq_card_adjoin_of_sameCycle hs, adjoin_sameCycle_swap_mul,
      ← cycleCount_eq_card_adjoin_of_sameCycle h] at hpar
    exact hpar rfl
  · intro h
    by_contra hs
    rw [cycleCount_eq_card_adjoin_of_not hs, adjoin_sameCycle_swap_mul,
      ← cycleCount_eq_card_adjoin_of_not h] at hpar
    exact hpar rfl

/-- Transposing two points on a common orbit splits it: the number of orbits
goes up by one. -/
theorem cycleCount_swap_mul_of_sameCycle (g : Perm D) {a b : D} (hab : a ≠ b)
    (h : g.SameCycle a b) : cycleCount (swap a b * g) = cycleCount g + 1 := by
  have hg := cycleCount_eq_card_adjoin_of_sameCycle h
  by_cases hs : (swap a b * g).SameCycle a b
  · have ht := cycleCount_eq_card_adjoin_of_sameCycle hs
    rw [adjoin_sameCycle_swap_mul] at ht
    exact absurd (by rw [ht, hg] : cycleCount (swap a b * g) % 2 = cycleCount g % 2)
      (cycleCount_swap_mul_mod_two g hab)
  · have ht := cycleCount_eq_card_adjoin_of_not hs
    rw [adjoin_sameCycle_swap_mul] at ht
    rw [ht, hg]

/-- Transposing two points on different orbits merges them: the number of orbits
goes down by one. -/
theorem cycleCount_swap_mul_of_not_sameCycle (g : Perm D) {a b : D} (hab : a ≠ b)
    (h : ¬ g.SameCycle a b) : cycleCount (swap a b * g) + 1 = cycleCount g := by
  have hg := cycleCount_eq_card_adjoin_of_not h
  by_cases hs : (swap a b * g).SameCycle a b
  · have ht := cycleCount_eq_card_adjoin_of_sameCycle hs
    rw [adjoin_sameCycle_swap_mul] at ht
    rw [ht, hg]
  · have ht := cycleCount_eq_card_adjoin_of_not hs
    rw [adjoin_sameCycle_swap_mul] at ht
    exact absurd (by rw [ht, hg] : cycleCount (swap a b * g) % 2 = cycleCount g % 2)
      (cycleCount_swap_mul_mod_two g hab)

end Transposition

end FourColor

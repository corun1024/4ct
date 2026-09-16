import FourColor.Euler

/-!
# Hypermap geometry

The geometrical reading of a hypermap, and the notions in which the Four Colour
Theorem is stated and proved.  Faces play a distinguished role: a dart is
thought of as a corner of a face, the `arity` of a dart is the size of its face,
and a *ring* is a list of darts meeting pairwise distinct faces (`Simple`) whose
consecutive darts are linked by `Rlink`.

The reference development is written with MathComp's boolean predicates and
`reflect` lemmas; here every geometrical notion is `Prop`-valued, face orbits
are `Equiv.Perm.SameCycle` of the face permutation, arity is
`Function.minimalPeriod`, simplicity is `List.Pairwise`, and cyclic paths are
`List.IsChain` together with a wrap-around link.

## Main definitions

* `Hypermap.Bridgeless`, `Hypermap.Loopless` — no face (resp. node) contains
  both ends of an E-link.
* `Hypermap.arity` — the size of the face of a dart.
* `Hypermap.Fband`, `Hypermap.Kernel` — the face closure of a list of darts and
  its complement.
* `Hypermap.Simple`, `FourColor.IsCyclicChain`, `Hypermap.Scycle` — face-simple
  lists, cyclic chains, and face-simple cyclic chains ("rings").
* `Hypermap.Rlink`, `Hypermap.Adj`, `Hypermap.Chordless` — the ring link
  relation, face adjacency, and chordless rings.
* `Hypermap.Plain`, `Hypermap.CubicOn`, `Hypermap.Cubic`,
  `Hypermap.Quasicubic`, `Hypermap.Precubic`, `Hypermap.Pentagonal` — the
  special geometries, together with the bundled property records used at the
  various points of the proof.
* `Hypermap.insertE` — the edge closure of a list of darts in a plain hypermap.

## Main results

* `Hypermap.bridgeless_dual`, `Hypermap.bridgeless_mirror`,
  `Hypermap.plain_dual`, `Hypermap.plain_mirror`, `Hypermap.cubic_mirror`,
  `Hypermap.precubic_mirror`, `Hypermap.arity_mirror` — the geometrical notions
  under the derived hypermaps.
* `Hypermap.simple_cons`, `Hypermap.simple_append`, `Hypermap.simple_rotate` —
  the combinatorics of face-simple lists.
* `Hypermap.exists_simple_rlink` — every `Rlink` path can be simplified to a
  face-simple one with the same endpoints.
* `Hypermap.cnode_iff_mem` — a duplicate-free N-cycle lists exactly one node
  orbit.
* `Hypermap.Plain.card_eq`, `Hypermap.Cubic.card_eq`, `Hypermap.cubic_Euler`,
  `Hypermap.quasicubic_Euler` — the special forms of the Euler formula for plain
  cubic connected hypermaps and for configuration maps.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/geometry.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D D' : Type*}

/-! ### Cyclic chains

MathComp's `cycle e p` asserts that `p` is an `e`-path that returns to its
starting point.  Here that is `List.IsChain` together with a link from the last
dart of the list back to the first one. -/

/-- `IsCyclicChain e p` holds when consecutive darts of `p` are `e`-linked, and
the last dart of `p` is `e`-linked to the first one.  This is MathComp's
`cycle e p`. -/
def IsCyclicChain (e : D → D → Prop) (p : List D) : Prop :=
  List.IsChain e p ∧ ∀ x ∈ p.getLast?, ∀ y ∈ p.head?, e x y

/-- The empty list is a cyclic chain. -/
@[simp] theorem isCyclicChain_nil (e : D → D → Prop) : IsCyclicChain e ([] : List D) := by
  simp [IsCyclicChain]

/-- A one-dart list is a cyclic chain exactly when its dart is a loop. -/
@[simp] theorem isCyclicChain_singleton {e : D → D → Prop} {x : D} :
    IsCyclicChain e [x] ↔ e x x := by
  simp [IsCyclicChain]

/-- A cyclic chain is in particular a chain. -/
theorem IsCyclicChain.isChain {e : D → D → Prop} {p : List D} (h : IsCyclicChain e p) :
    List.IsChain e p := h.1

/-- A list with a head is a cyclic chain when it is a chain whose last dart
links back to its first one. -/
theorem isCyclicChain_cons {e : D → D → Prop} {x : D} {t : List D} :
    IsCyclicChain e (x :: t) ↔
      List.IsChain e (x :: t) ∧ e ((x :: t).getLast (List.cons_ne_nil x t)) x := by
  constructor
  · rintro ⟨hc, hw⟩
    exact ⟨hc, hw _ (List.getLast?_eq_some_getLast (List.cons_ne_nil x t)) x rfl⟩
  · rintro ⟨hc, hw⟩
    refine ⟨hc, fun a ha b hb => ?_⟩
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x t), Option.mem_def,
      Option.some.injEq] at ha
    rw [Option.mem_def] at hb
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst ha; subst hb
    exact hw

/-- A list with a last dart is a cyclic chain when it is a chain whose last
dart links back to its first one. -/
theorem isCyclicChain_concat {e : D → D → Prop} {x : D} {t : List D} :
    IsCyclicChain e (t ++ [x]) ↔
      List.IsChain e (t ++ [x]) ∧ ∀ b ∈ (t ++ [x]).head?, e x b := by
  rw [IsCyclicChain]
  constructor
  · rintro ⟨hc, hw⟩
    exact ⟨hc, fun b hb => hw x List.getLast?_concat b hb⟩
  · rintro ⟨hc, hw⟩
    refine ⟨hc, fun a ha b hb => ?_⟩
    rw [List.getLast?_concat, Option.mem_def, Option.some.injEq] at ha
    subst ha
    exact hw b hb

/-- Moving the head of a cyclic chain to its end again gives a cyclic chain;
this is one step of rotation. -/
theorem isCyclicChain_cons_iff_concat {e : D → D → Prop} {x : D} {t : List D} :
    IsCyclicChain e (x :: t) ↔ IsCyclicChain e (t ++ [x]) := by
  match t with
  | [] => simp
  | y :: t =>
    have hsplit : List.IsChain e ((y :: t) ++ [x]) ↔
        List.IsChain e (y :: t) ∧ e ((y :: t).getLast (List.cons_ne_nil y t)) x := by
      rw [List.isChain_append]
      constructor
      · rintro ⟨h₁, -, h₃⟩
        exact ⟨h₁, h₃ _ (List.getLast?_eq_some_getLast (List.cons_ne_nil y t)) x rfl⟩
      · rintro ⟨h₁, h₂⟩
        refine ⟨h₁, List.isChain_singleton x, fun a ha b hb => ?_⟩
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil y t), Option.mem_def,
          Option.some.injEq] at ha
        rw [Option.mem_def] at hb
        simp only [List.head?_cons, Option.some.injEq] at hb
        subst ha; subst hb
        exact h₂
    rw [isCyclicChain_cons, isCyclicChain_concat, hsplit, List.isChain_cons_cons,
      List.getLast_cons_cons]
    constructor
    · rintro ⟨⟨hxy, hc⟩, hw⟩
      refine ⟨⟨hc, hw⟩, fun b hb => ?_⟩
      rw [Option.mem_def] at hb
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hb
      subst hb
      exact hxy
    · rintro ⟨⟨hc, hw⟩, hxy⟩
      exact ⟨⟨hxy y (by simp), hc⟩, hw⟩

/-- Rotating a list by a multiple of its length does not change it. -/
theorem rotate_length_mul (l : List D) (k : ℕ) : l.rotate (l.length * k) = l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← List.rotate_rotate, ih, List.rotate_length]

/-- Being a cyclic chain is invariant under rotation. -/
@[simp] theorem isCyclicChain_rotate {e : D → D → Prop} {p : List D} {n : ℕ} :
    IsCyclicChain e (p.rotate n) ↔ IsCyclicChain e p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    match p with
    | [] => simp
    | x :: t => rw [List.rotate_cons_succ, ih, isCyclicChain_cons_iff_concat]

/-! ### Cyclic successors -/

/-- `y` is the cyclic successor of `x` in `r`: some rotation of `r` starts with
`x` followed by `y` (with `y = x` when `r` has a single dart). -/
def CyclicNext (r : List D) (x y : D) : Prop :=
  ∃ (n : ℕ) (t : List D), r.rotate n = x :: t ∧ y = t.headD x

/-- Cyclic successors do not change under rotation. -/
@[simp] theorem cyclicNext_rotate {r : List D} {n : ℕ} {x y : D} :
    CyclicNext (r.rotate n) x y ↔ CyclicNext r x y := by
  constructor
  · rintro ⟨m, t, ht, hy⟩
    exact ⟨n + m, t, by rwa [← List.rotate_rotate], hy⟩
  · rintro ⟨m, t, ht, hy⟩
    have hLpos : 0 < r.length := by
      match r with
      | [] => simp at ht
      | _ :: _ => simp
    have hle : n ≤ r.length * (n + 1) + m := by
      have h1 : n + 1 ≤ r.length * (n + 1) := Nat.le_mul_of_pos_left _ hLpos
      omega
    refine ⟨r.length * (n + 1) + m - n, t, ?_, hy⟩
    rw [List.rotate_rotate, Nat.add_sub_cancel' hle, ← List.rotate_rotate,
      rotate_length_mul, ht]

namespace Hypermap

/-! ### Bridges and loops -/

section BridgeAndLoopLess

variable (G : Hypermap D)

/-- `G` is bridgeless when no face of `G` contains both ends of an E-link. -/
def Bridgeless : Prop := ∀ x : D, ¬ G.CFace x (G.edge x)

/-- `G` is loopless when no node of `G` contains both ends of an E-link. -/
def Loopless : Prop := ∀ x : D, ¬ G.CNode x (G.edge x)

end BridgeAndLoopLess

/-- The dual of `G` is bridgeless exactly when `G` is loopless: dualising
exchanges nodes and faces. -/
theorem bridgeless_dual (G : Hypermap D) : G.dual.Bridgeless ↔ G.Loopless := by
  simp only [Bridgeless, Loopless, CFace, CNode, dual_face, dual_edge, sameCycle_inv]
  constructor
  · intro h x hx
    exact h (G.edge x) (by simpa using hx.symm)
  · intro h y hy
    exact h ((G.edge⁻¹ : Perm D) y) (by simpa using hy.symm)

/-- Mirroring preserves bridgelessness. -/
theorem bridgeless_mirror (G : Hypermap D) : G.mirror.Bridgeless ↔ G.Bridgeless := by
  have key : ∀ y : D, G.mirror.CFace y (G.mirror.edge y) ↔ G.CFace y (G.node y) := by
    intro y
    change (G.face⁻¹ : Perm D).SameCycle y ((G.face * G.node) y) ↔ _
    rw [Perm.mul_apply, sameCycle_inv, sameCycle_apply_right]
  simp only [Bridgeless, key]
  constructor
  · intro h x hx
    refine h (G.face (G.edge x)) ?_
    rw [G.edgeK]
    exact sameCycle_apply_left.mpr hx.symm
  · intro h y hy
    refine h (G.node y) ?_
    have he : (G.face⁻¹ : Perm D) y = G.edge (G.node y) :=
      Perm.inv_eq_iff_eq.mpr (G.nodeK y).symm
    rw [← he]
    refine sameCycle_apply_right.mp ?_
    simpa using hy.symm

/-! ### Arity

Edge and node arities are fixed by the special geometries below, so *the* arity
of a dart is its face arity: the size of its face. -/

/-- The arity of a dart: the number of darts in its face. -/
noncomputable def arity (G : Hypermap D) (x : D) : ℕ := Function.minimalPeriod G.face x

/-- Every dart of a finite type is a periodic point of any permutation. -/
theorem mem_periodicPts [Finite D] (f : Perm D) (x : D) : x ∈ Function.periodicPts f :=
  Function.mk_mem_periodicPts (orderOf_pos f)
    (by change f^[orderOf f] x = x; rw [Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl)

/-- Inverting a permutation does not change minimal periods. -/
theorem minimalPeriod_inv (f : Perm D) (x : D) :
    Function.minimalPeriod (f⁻¹ : Perm D) x = Function.minimalPeriod f x := by
  have key : ∀ (g : Perm D) (n : ℕ), Function.IsPeriodicPt (g : D → D) n x →
      Function.IsPeriodicPt ((g⁻¹ : Perm D) : D → D) n x := by
    intro g n hg
    have h' : ((g ^ n : Perm D) : D → D) x = x := hg
    have h'' : (((g ^ n : Perm D)⁻¹ : Perm D) : D → D) x = x := by
      conv_lhs => rw [← h']
      simp
    change (((g⁻¹ : Perm D) ^ n : Perm D) : D → D) x = x
    rw [inv_pow]
    exact h''
  refine Nat.dvd_antisymm ?_ ?_
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    exact key f _ (Function.isPeriodicPt_minimalPeriod _ x)
  · rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    have h := key f⁻¹ _ (Function.isPeriodicPt_minimalPeriod ((f⁻¹ : Perm D) : D → D) x)
    simpa using h

section Arity

variable [Finite D] (G : Hypermap D)

/-- Faces are nonempty. -/
theorem arity_pos (x : D) : 0 < G.arity x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts G.face x)

omit [Finite D] in
/-- Iterating `face` arity-many times returns to the same dart. -/
@[simp] theorem iterate_face_arity (x : D) : G.face^[G.arity x] x = x :=
  Function.iterate_minimalPeriod

/-- Arity is constant along a face. -/
theorem arity_iterate_face (n : ℕ) (x : D) : G.arity (G.face^[n] x) = G.arity x :=
  Function.minimalPeriod_apply_iterate (mem_periodicPts G.face x) n

/-- Arity is constant along a face. -/
@[simp] theorem arity_face (x : D) : G.arity (G.face x) = G.arity x :=
  Function.minimalPeriod_apply (mem_periodicPts G.face x)

/-- Darts in the same face have the same arity. -/
theorem arity_cface {x y : D} (h : G.CFace x y) : G.arity x = G.arity y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, Perm.coe_pow, arity_iterate_face]

omit [Finite D] in
/-- Completing a partial turn around a face. -/
theorem iterate_face_arity_sub {n : ℕ} {x : D} (h : n ≤ G.arity x) :
    G.face^[G.arity x - n] (G.face^[n] x) = x := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel h, iterate_face_arity]

omit [Finite D] in
/-- Mirroring preserves arity. -/
@[simp] theorem arity_mirror (x : D) : G.mirror.arity x = G.arity x := by
  rw [arity, arity, mirror_face, minimalPeriod_inv]

end Arity

/-! ### Face bands, kernels and simple lists -/

section FacePaths

variable (G : Hypermap D)

/-- The face closure of `p`: darts whose face meets `p`. -/
def Fband (p : List D) (x : D) : Prop := ∃ y ∈ p, G.CFace x y

/-- The complement of the face closure of `p`.  It is used with `p` the outer
ring of a configuration, where it is the union of the inner faces. -/
def Kernel (p : List D) (x : D) : Prop := ¬ G.Fband p x

/-- A list of darts meeting pairwise distinct faces. -/
def Simple (p : List D) : Prop := p.Pairwise fun x y => ¬ G.CFace x y

/-- A face-simple `e`-cycle. -/
def Scycle (e : D → D → Prop) (p : List D) : Prop := IsCyclicChain e p ∧ G.Simple p

variable {G}

/-- The band of the empty list is empty. -/
@[simp] theorem fband_nil (x : D) : ¬ G.Fband [] x := by simp [Fband]

/-- The band of a list with a head. -/
@[simp] theorem fband_cons {y : D} {p : List D} {x : D} :
    G.Fband (y :: p) x ↔ G.CFace x y ∨ G.Fband p x := by
  simp only [Fband, List.mem_cons]
  constructor
  · rintro ⟨z, rfl | hz, hxz⟩
    exacts [Or.inl hxz, Or.inr ⟨z, hz, hxz⟩]
  · rintro (hxy | ⟨z, hz, hxz⟩)
    exacts [⟨y, Or.inl rfl, hxy⟩, ⟨z, Or.inr hz, hxz⟩]

/-- The band of a concatenation is the union of the bands. -/
@[simp] theorem fband_append {p q : List D} {x : D} :
    G.Fband (p ++ q) x ↔ G.Fband p x ∨ G.Fband q x := by
  simp only [Fband, List.mem_append]
  constructor
  · rintro ⟨y, hy | hy, hxy⟩
    exacts [Or.inl ⟨y, hy, hxy⟩, Or.inr ⟨y, hy, hxy⟩]
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    exacts [⟨y, Or.inl hy, hxy⟩, ⟨y, Or.inr hy, hxy⟩]

/-- The band of a list extended on the right. -/
theorem fband_concat {p : List D} {y x : D} :
    G.Fband (p ++ [y]) x ↔ G.CFace x y ∨ G.Fband p x := by
  simp [or_comm]

/-- Reversing a list does not change its band. -/
@[simp] theorem fband_reverse {p : List D} {x : D} : G.Fband p.reverse x ↔ G.Fband p x := by
  simp [Fband]

/-- Rotating a list does not change its band. -/
@[simp] theorem fband_rotate {p : List D} {n : ℕ} {x : D} :
    G.Fband (p.rotate n) x ↔ G.Fband p x := by
  simp [Fband, List.mem_rotate]

/-- Every dart of `p` lies in the band of `p`. -/
theorem fband_of_mem {p : List D} {x : D} (hx : x ∈ p) : G.Fband p x :=
  ⟨x, hx, SameCycle.refl _ _⟩

/-- The band of a list only depends on the face of a dart. -/
theorem Fband.congr {p : List D} {x y : D} (h : G.CFace x y) :
    G.Fband p x ↔ G.Fband p y :=
  ⟨fun ⟨z, hz, hxz⟩ => ⟨z, hz, h.symm.trans hxz⟩, fun ⟨z, hz, hyz⟩ => ⟨z, hz, h.trans hyz⟩⟩

/-- The band of a list is closed under `face`. -/
@[simp] theorem fband_face {p : List D} {x : D} : G.Fband p (G.face x) ↔ G.Fband p x :=
  Fband.congr (sameCycle_apply_right.mpr (SameCycle.refl G.face x)).symm

/-- The kernel of a list only depends on the face of a dart. -/
theorem Kernel.congr {p : List D} {x y : D} (h : G.CFace x y) :
    G.Kernel p x ↔ G.Kernel p y := not_congr (Fband.congr h)

/-- The kernel of a list is closed under `face`. -/
@[simp] theorem kernel_face {p : List D} {x : D} : G.Kernel p (G.face x) ↔ G.Kernel p x :=
  not_congr fband_face

/-- Darts in the kernel of `p` are not in `p`. -/
theorem not_mem_of_kernel {p : List D} {x : D} (h : G.Kernel p x) : x ∉ p :=
  fun hx => h (fband_of_mem hx)

/-- Meeting the band of another list is a symmetric relation. -/
theorem exists_fband_comm {p q : List D} :
    (∃ x ∈ q, G.Fband p x) ↔ (∃ x ∈ p, G.Fband q x) := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, hxy.symm⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, hxy.symm⟩

/-- Replacing a dart by one in the same face does not change a band. -/
theorem fband_replicate_congr {x y : D} (h : G.CFace x y) (n : ℕ) (z : D) :
    G.Fband (List.replicate n x) z ↔ G.Fband (List.replicate n y) z := by
  have hz : G.CFace z x ↔ G.CFace z y := ⟨fun hzx => hzx.trans h, fun hzy => hzy.trans h.symm⟩
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, fband_cons, ih, hz]

/-- The empty list is face-simple. -/
@[simp] theorem simple_nil : G.Simple ([] : List D) := List.Pairwise.nil

/-- A list with a head is face-simple exactly when its head lies outside the band
of its tail, which is itself face-simple. -/
@[simp] theorem simple_cons {x : D} {p : List D} :
    G.Simple (x :: p) ↔ ¬ G.Fband p x ∧ G.Simple p := by
  rw [Simple, List.pairwise_cons]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun ⟨y, hy, hxy⟩ => h₁ y hy hxy, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨fun y hy hxy => h₁ ⟨y, hy, hxy⟩, h₂⟩⟩

/-- A face-simple list has no repetitions. -/
theorem Simple.nodup {p : List D} (h : G.Simple p) : p.Nodup := by
  refine List.Pairwise.imp ?_ h
  intro a b hab hab'
  exact hab (by subst hab'; exact SameCycle.refl _ _)

/-- The tail of a face-simple list is face-simple. -/
theorem Simple.of_cons {x : D} {p : List D} (h : G.Simple (x :: p)) : G.Simple p :=
  (simple_cons.mp h).2

/-- The head of a face-simple list is outside the band of its tail. -/
theorem Simple.not_fband {x : D} {p : List D} (h : G.Simple (x :: p)) : ¬ G.Fband p x :=
  (simple_cons.mp h).1

/-- A concatenation is face-simple exactly when both parts are and their bands
are disjoint from each other's darts. -/
theorem simple_append {p q : List D} :
    G.Simple (p ++ q) ↔ G.Simple p ∧ G.Simple q ∧ ∀ x ∈ p, ¬ G.Fband q x := by
  rw [Simple, List.pairwise_append]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun x hx ⟨y, hy, hxy⟩ => h₃ x hx y hy hxy⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun x hx y hy hxy => h₃ x hx ⟨y, hy, hxy⟩⟩⟩

/-- A list extended on the right is face-simple exactly when the new dart lies
outside the band of the old list, which is itself face-simple. -/
theorem simple_concat {p : List D} {x : D} :
    G.Simple (p ++ [x]) ↔ ¬ G.Fband p x ∧ G.Simple p := by
  rw [simple_append]
  constructor
  · rintro ⟨hp, -, h⟩
    refine ⟨fun hx => ?_, hp⟩
    obtain ⟨y, hy, hxy⟩ := hx
    exact h y hy ⟨x, List.mem_singleton_self x, hxy.symm⟩
  · rintro ⟨hx, hp⟩
    refine ⟨hp, List.pairwise_singleton _ _, fun y hy hy' => hx ?_⟩
    obtain ⟨z, hz, hyz⟩ := hy'
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨y, hy, hyz.symm⟩

/-- Face-simplicity is invariant under permutation of the list. -/
theorem Simple.perm {p q : List D} (h : G.Simple p) (hpq : p.Perm q) : G.Simple q := by
  refine List.Pairwise.perm h hpq ?_
  intro x y hxy hyx
  exact hxy hyx.symm

/-- Face-simplicity does not depend on the order of two concatenated parts. -/
theorem simple_append_comm {p q : List D} : G.Simple (p ++ q) ↔ G.Simple (q ++ p) :=
  ⟨fun h => h.perm List.perm_append_comm, fun h => h.perm List.perm_append_comm⟩

/-- Rotating a list preserves face-simplicity. -/
@[simp] theorem simple_rotate {p : List D} {n : ℕ} : G.Simple (p.rotate n) ↔ G.Simple p :=
  ⟨fun h => h.perm (List.rotate_perm p n), fun h => h.perm (List.rotate_perm p n).symm⟩

/-- Reversing a list preserves face-simplicity. -/
@[simp] theorem simple_reverse {p : List D} : G.Simple p.reverse ↔ G.Simple p :=
  ⟨fun h => h.perm (List.reverse_perm p), fun h => h.perm (List.reverse_perm p).symm⟩

/-- Darts of a face-simple list lying in a common face are equal. -/
theorem Simple.eq_of_cface {p : List D} (h : G.Simple p) {x y : D} (hx : x ∈ p) (hy : y ∈ p)
    (hxy : G.CFace x y) : x = y := by
  induction p with
  | nil => simp at hx
  | cons a t ih =>
    rw [simple_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd ⟨y, hy', hxy⟩ h.1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd ⟨x, hx', hxy.symm⟩ h.1
      · exact ih h.2 hx' hy'

/-- In a face-simple list, the dart meeting the face of `x` is unique.  This is
the content of the reference's ring projection `fproj`. -/
theorem Simple.existsUnique_cface {p : List D} (h : G.Simple p) {x : D} (hx : G.Fband p x) :
    ∃! y, y ∈ p ∧ G.CFace x y := by
  obtain ⟨y, hy, hxy⟩ := hx
  refine ⟨y, ⟨hy, hxy⟩, ?_⟩
  rintro z ⟨hz, hxz⟩
  exact h.eq_of_cface hz hy (hxz.symm.trans hxy)

/-! #### The face projection

The dart of a list that lies on the face of a given dart.  When the list is
face-simple this picks out a unique representative of each face it meets, which
is how configurations are compared face by face.  Off the list the projection
falls back on a canonical representative of the face, so that it depends only on
the face in every case.
-/

/-- A canonical representative of the face of a dart. -/
noncomputable def froot (x : D) : D := (Quotient.mk (SameCycle.setoid G.face) x).out

theorem cface_froot (x : D) : G.CFace x (G.froot x) :=
  (Quotient.mk_out (s := SameCycle.setoid G.face) x).symm

theorem froot_congr {x y : D} (h : G.CFace x y) : G.froot x = G.froot y :=
  congrArg Quotient.out (Quotient.sound h)

open scoped Classical in
/-- The dart of `p` that lies on the face of `x`, or a canonical representative
of that face if there is none. -/
noncomputable def fproj (p : List D) (x : D) : D :=
  (p.find? fun y => decide (G.CFace x y)).getD (G.froot x)

open scoped Classical in
private theorem find?_cface_isSome {p : List D} {x : D} (h : G.Fband p x) :
    ∃ y, (p.find? fun y => decide (G.CFace x y)) = some y := by
  obtain ⟨z, hz, hxz⟩ := h
  match hf : p.find? fun y => decide (G.CFace x y) with
  | some y => exact ⟨y, rfl⟩
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (hf z hz) (by simpa using hxz)

/-- The projection of a dart of the face band lies on the list. -/
theorem fproj_mem {p : List D} {x : D} (h : G.Fband p x) : G.fproj p x ∈ p := by
  classical
  obtain ⟨y, hy⟩ := G.find?_cface_isSome h
  rw [fproj, hy, Option.getD_some]
  exact List.mem_of_find?_eq_some hy

/-- A dart shares its face with its projection. -/
theorem cface_fproj {p : List D} (x : D) : G.CFace x (G.fproj p x) := by
  classical
  match hp : p.find? fun y => decide (G.CFace x y) with
  | some z =>
    rw [fproj, hp, Option.getD_some]
    simpa using List.find?_some hp
  | none =>
    rw [fproj, hp, Option.getD_none]
    exact G.cface_froot x

/-- The projection only depends on the face. -/
theorem fproj_congr {p : List D} {x y : D} (h : G.CFace x y) :
    G.fproj p x = G.fproj p y := by
  classical
  have hpred : (fun z => decide (G.CFace x z)) = fun z => decide (G.CFace y z) := by
    funext z
    simp only [decide_eq_decide]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  rw [fproj, fproj, hpred, G.froot_congr h]

/-- In a face-simple list the projection is the unique dart of the list on the
face. -/
theorem Simple.fproj_eq {p : List D} (hs : G.Simple p) {x y : D} (hy : y ∈ p)
    (h : G.CFace x y) : G.fproj p x = y :=
  hs.eq_of_cface (G.fproj_mem ⟨y, hy, h⟩) hy ((G.cface_fproj x).symm.trans h)

/-- On a face-simple list the projection is the identity. -/
theorem Simple.fproj_self {p : List D} (hs : G.Simple p) {x : D} (hx : x ∈ p) :
    G.fproj p x = x :=
  hs.fproj_eq hx (Equiv.Perm.SameCycle.refl _ _)

/-- Face-simplicity transfers along a map preserving face orbits. -/
theorem simple_map {H : Hypermap D'} {f : D → D'}
    (hf : ∀ x y : D, H.CFace (f x) (f y) ↔ G.CFace x y) (p : List D) :
    H.Simple (p.map f) ↔ G.Simple p := by
  simp only [Simple, List.pairwise_map, hf]

/-- Face-simplicity says exactly that the face classes of the darts of `p` are
pairwise distinct; this is the reference's definition of `simple`. -/
theorem simple_iff_nodup_map {p : List D} :
    G.Simple p ↔ (p.map (Quotient.mk (SameCycle.setoid G.face))).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  constructor
  · refine fun h => List.Pairwise.imp ?_ h
    intro a b hab hq
    exact hab (Quotient.exact hq)
  · refine fun h => List.Pairwise.imp ?_ h
    intro a b hab hface
    exact hab (Quotient.sound hface)

private theorem nodup_of_mem_iff {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) (hlen : l₁.length = l₂.length) (h : l₁.Nodup) :
    l₂.Nodup := by
  have h1 : l₁.toFinset = l₂.toFinset := by
    ext a
    simp [hmem a]
  have h2 : l₂.dedup.length = l₂.length := by
    rw [← List.card_toFinset, ← h1, List.card_toFinset, List.dedup_eq_self.mpr h, hlen]
  exact List.nodup_iff_length_dedup_eq.mpr h2

/-- The classes a list meets are the classes of its darts. -/
theorem mem_map_quotient_iff_fband {p : List D} {x : D} :
    Quotient.mk (SameCycle.setoid G.face) x ∈ p.map (Quotient.mk (SameCycle.setoid G.face))
      ↔ G.Fband p x := by
  constructor
  · intro h
    obtain ⟨y, hy, hq⟩ := List.mem_map.mp h
    exact ⟨y, hy, (Quotient.exact hq).symm⟩
  · rintro ⟨y, hy, hxy⟩
    exact List.mem_map.mpr ⟨y, hy, (Quotient.sound hxy.symm)⟩

open scoped Classical in
/-- A face-simple list meets exactly as many faces as it has darts: the
reference's `simple_fcard_fband`. -/
theorem Simple.card_faces {p : List D} (h : G.Simple p) :
    (p.map (Quotient.mk (SameCycle.setoid G.face))).toFinset.card = p.length := by
  rw [List.toFinset_card_of_nodup (G.simple_iff_nodup_map.mp h), List.length_map]

open scoped Classical in
/-- The faces a list meets are exactly the classes of the darts of its face
band. -/
theorem mem_toFinset_map_quotient_iff {p : List D} {x : D} :
    Quotient.mk (SameCycle.setoid G.face) x
        ∈ (p.map (Quotient.mk (SameCycle.setoid G.face))).toFinset ↔ G.Fband p x := by
  rw [List.mem_toFinset]
  exact G.mem_map_quotient_iff_fband

/-- Two lists with the same face band and the same length are face-simple
together: the reference's `eq_simple`. -/
theorem simple_iff_of_fband_eq {p q : List D} (hband : ∀ x, G.Fband p x ↔ G.Fband q x)
    (hlen : p.length = q.length) : G.Simple p ↔ G.Simple q := by
  classical
  have hsub : ∀ r s : List D, (∀ x, G.Fband r x ↔ G.Fband s x) →
      ∀ c ∈ r.map (Quotient.mk (SameCycle.setoid G.face)),
        c ∈ s.map (Quotient.mk (SameCycle.setoid G.face)) := by
    intro r s h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
    exact G.mem_map_quotient_iff_fband.mpr ((h y).mp (G.fband_of_mem hy))
  have hmem : ∀ c, c ∈ p.map (Quotient.mk (SameCycle.setoid G.face)) ↔
      c ∈ q.map (Quotient.mk (SameCycle.setoid G.face)) := by
    intro c
    refine Quotient.inductionOn c fun x => ?_
    rw [G.mem_map_quotient_iff_fband, G.mem_map_quotient_iff_fband]
    exact hband x
  have hlen' : (p.map (Quotient.mk (SameCycle.setoid G.face))).length
      = (q.map (Quotient.mk (SameCycle.setoid G.face))).length := by simp [hlen]
  rw [simple_iff_nodup_map, simple_iff_nodup_map]
  exact ⟨fun h => nodup_of_mem_iff hmem hlen' h,
    fun h => nodup_of_mem_iff (fun c => (hmem c).symm) hlen'.symm h⟩

/-! #### Rings: face-simple cycles -/

/-- A face-simple cycle is a cycle. -/
theorem Scycle.isCyclicChain {e : D → D → Prop} {p : List D} (h : G.Scycle e p) :
    IsCyclicChain e p := h.1

/-- A face-simple cycle is face-simple. -/
theorem Scycle.simple {e : D → D → Prop} {p : List D} (h : G.Scycle e p) : G.Simple p := h.2

/-- A face-simple cycle has no repetitions. -/
theorem Scycle.nodup {e : D → D → Prop} {p : List D} (h : G.Scycle e p) : p.Nodup := h.2.nodup

/-- Rotating a list preserves being a face-simple cycle. -/
@[simp] theorem scycle_rotate {e : D → D → Prop} {p : List D} {n : ℕ} :
    G.Scycle e (p.rotate n) ↔ G.Scycle e p := by
  rw [Scycle, Scycle, isCyclicChain_rotate, simple_rotate]

end FacePaths

end Hypermap

/-! ### Cycles of a permutation as lists

A duplicate-free cyclic chain for `fun x y => y = f x` lists exactly one orbit of
`f`; this is MathComp's `ufcycle f r`, the shape of a configuration perimeter. -/

section ListCycles

/-- Every dart of an `f`-chain lies on the cycle of its head. -/
theorem sameCycle_of_isChain_cons {f : Perm D} : ∀ (t : List D) (a : D),
    List.IsChain (fun u v => v = f u) (a :: t) → ∀ z ∈ a :: t, f.SameCycle a z := by
  intro t
  induction t with
  | nil =>
    intro a _ z hz
    rw [List.mem_singleton] at hz
    subst hz
    exact SameCycle.refl _ _
  | cons b t ih =>
    intro a h z hz
    obtain ⟨hab, hchain⟩ := List.isChain_cons_cons.mp h
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact SameCycle.refl _ _
    · have hbz := ih b hchain z hz'
      rw [hab] at hbz
      exact sameCycle_apply_left.mp hbz

/-- Any two darts of an `f`-chain lie on a common cycle. -/
theorem sameCycle_of_mem_isChain {f : Perm D} {l : List D}
    (h : List.IsChain (fun u v => v = f u) l) {x y : D} (hx : x ∈ l) (hy : y ∈ l) :
    f.SameCycle x y := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    exact (sameCycle_of_isChain_cons t a h x hx).symm.trans (sameCycle_of_isChain_cons t a h y hy)

/-- The darts of an `f`-cycle are closed under `f`. -/
theorem mem_of_isCyclicChain {f : D → D} {r : List D}
    (h : IsCyclicChain (fun u v => v = f u) r) {x : D} (hx : x ∈ r) : f x ∈ r := by
  obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hx
  cases p₂ with
  | cons z p₂ =>
    have hc := h.isChain
    rw [List.isChain_append_cons_cons] at hc
    rw [← hc.2.1]
    simp
  | nil =>
    have hne : p₁ ++ [x] ≠ [] := by simp
    have hb : (p₁ ++ [x]).head? = some ((p₁ ++ [x]).head hne) := List.head?_eq_some_head hne
    have hbx := h.2 x List.getLast?_concat _ hb
    rw [← hbx]
    exact List.head_mem hne

end ListCycles

namespace Hypermap

section NodeCycles

variable [Finite D] {G : Hypermap D} {r : List D}

/-- The darts of an N-cycle are exactly the darts of one node orbit. -/
theorem cnode_iff_mem (hcyc : IsCyclicChain (fun u v => v = G.node u) r) {x : D} (hx : x ∈ r)
    (y : D) : G.CNode x y ↔ y ∈ r := by
  constructor
  · intro hxy
    have hxy' : Relation.ReflTransGen (fun a b => b = G.node a) x y :=
      (sameCycle_iff_reflTransGen G.node x y).mp hxy
    clear hxy
    induction hxy' with
    | refl => exact hx
    | tail _ hbc ih =>
      rw [hbc]
      exact mem_of_isCyclicChain hcyc ih
  · intro hy
    exact sameCycle_of_mem_isChain hcyc.isChain hx hy

/-- The complement of an N-cycle is closed under `node`. -/
theorem node_mem_iff_mem (hcyc : IsCyclicChain (fun u v => v = G.node u) r) (x : D) :
    G.node x ∈ r ↔ x ∈ r := by
  constructor
  · intro h
    exact (cnode_iff_mem hcyc h x).mp (sameCycle_apply_left.mpr (SameCycle.refl _ _))
  · intro h
    exact mem_of_isCyclicChain hcyc h

end NodeCycles

end Hypermap

namespace Hypermap

/-! ### Special geometries

A *plain* hypermap has two-dart edges, a *cubic* one has three-dart nodes, and a
*precubic* one has nodes of at most three darts.  Cubicity is also considered
relative to a set of darts, since a configuration map is only cubic away from
its perimeter. -/

/-- A permutation squares to the identity exactly when it is an involution. -/
private theorem pow_two_eq_one_iff (f : Perm D) :
    f ^ 2 = 1 ↔ ∀ x : D, f (f x) = x := by
  have hf : (f ^ 2 : Perm D) = f * f := pow_two f
  constructor
  · intro h x
    have hx : (f ^ 2 : Perm D) x = x := by rw [h]; rfl
    rwa [hf, Perm.mul_apply] at hx
  · intro h
    ext x
    rw [hf, Perm.mul_apply, h]
    rfl

/-- A permutation cubes to the identity exactly when it is of order three. -/
private theorem pow_three_eq_one_iff (f : Perm D) :
    f ^ 3 = 1 ↔ ∀ x : D, f (f (f x)) = x := by
  have hf : (f ^ 3 : Perm D) = f * (f * f) := by
    rw [pow_succ, pow_two, mul_assoc]
  constructor
  · intro h x
    have hx : (f ^ 3 : Perm D) x = x := by rw [h]; rfl
    rwa [hf, Perm.mul_apply, Perm.mul_apply] at hx
  · intro h
    ext x
    rw [hf, Perm.mul_apply, Perm.mul_apply, h]
    rfl

/-- A permutation and its inverse have the same fixed darts. -/
private theorem inv_ne_iff (f : Perm D) :
    (∀ x : D, (f⁻¹ : Perm D) x ≠ x) ↔ ∀ x : D, f x ≠ x := by
  constructor
  · intro h x hx
    exact h x (Perm.inv_eq_iff_eq.mpr hx.symm)
  · intro h x hx
    exact h x (Perm.inv_eq_iff_eq.mp hx).symm

section SpecialMaps

variable (G : Hypermap D)

/-- A plain hypermap: every edge (E-cycle) consists of exactly two darts. -/
structure Plain : Prop where
  /-- `edge` is an involution. -/
  edge_edge : ∀ x : D, G.edge (G.edge x) = x
  /-- `edge` has no fixed dart. -/
  edge_ne : ∀ x : D, G.edge x ≠ x

/-- `G` is cubic on `A`: every node meeting `A` consists of exactly three
darts. -/
structure CubicOn (A : Set D) : Prop where
  /-- `node` is of order three on `A`. -/
  node_node_node : ∀ x ∈ A, G.node (G.node (G.node x)) = x
  /-- `node` has no fixed dart in `A`. -/
  node_ne : ∀ x ∈ A, G.node x ≠ x

/-- A cubic hypermap: every node consists of exactly three darts. -/
def Cubic : Prop := G.CubicOn Set.univ

/-- `G` is quasicubic for `r`: it is cubic away from the darts of `r`. -/
def Quasicubic (r : List D) : Prop := G.CubicOn {x | x ∉ r}

/-- A precubic hypermap: every node consists of at most three darts. -/
def Precubic : Prop := ∀ x : D, Function.minimalPeriod G.node x ≤ 3

/-- A pentagonal hypermap: every face consists of at least five darts. -/
def Pentagonal : Prop := ∀ x : D, 4 < G.arity x

variable {G}

/-- Plainness, unbundled. -/
theorem plain_iff : G.Plain ↔ (∀ x : D, G.edge (G.edge x) = x) ∧ ∀ x : D, G.edge x ≠ x :=
  ⟨fun h => ⟨h.edge_edge, h.edge_ne⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Cubicity, unbundled. -/
theorem cubic_iff :
    G.Cubic ↔ (∀ x : D, G.node (G.node (G.node x)) = x) ∧ ∀ x : D, G.node x ≠ x :=
  ⟨fun h => ⟨fun x => h.1 x (Set.mem_univ x), fun x => h.2 x (Set.mem_univ x)⟩,
   fun h => ⟨fun x _ => h.1 x, fun x _ => h.2 x⟩⟩

/-- In a plain hypermap `node (face x) = edge x`. -/
theorem Plain.node_face (h : G.Plain) (x : D) : G.node (G.face x) = G.edge x := by
  have hx := congrArg (G.edge : D → D) (G.faceK x)
  rwa [h.edge_edge] at hx

/-- The edge permutation of a plain hypermap is an involution. -/
theorem Plain.edge_pow_two (h : G.Plain) : G.edge ^ 2 = 1 :=
  (pow_two_eq_one_iff G.edge).mpr h.edge_edge

/-- The edge orbit of a dart of a plain hypermap. -/
theorem Plain.cedge_iff [Finite D] (h : G.Plain) {x y : D} :
    G.CEdge x y ↔ y = x ∨ y = G.edge x := by
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    have key : ∀ m : ℕ, (G.edge ^ m) x = x ∨ (G.edge ^ m) x = G.edge x := by
      intro m
      induction m with
      | zero => exact Or.inl (by simp)
      | succ m ih =>
        rcases ih with hm | hm
        · exact Or.inr (by rw [pow_succ', Perm.mul_apply, hm])
        · exact Or.inl (by rw [pow_succ', Perm.mul_apply, hm, h.edge_edge])
    rcases key n with hk | hk
    exacts [Or.inl (by rw [← hn, hk]), Or.inr (by rw [← hn, hk])]
  · rintro (rfl | rfl)
    exacts [SameCycle.refl _ _, sameCycle_apply_right.mpr (SameCycle.refl _ _)]

/-- Edges of a plain hypermap have exactly two darts. -/
theorem Plain.minimalPeriod_edge (h : G.Plain) (x : D) :
    Function.minimalPeriod G.edge x = 2 := by
  have h2 : Function.IsPeriodicPt (G.edge : D → D) 2 x := by
    change G.edge (G.edge x) = x
    exact h.edge_edge x
  rcases (Nat.dvd_prime Nat.prime_two).mp h2.minimalPeriod_dvd with h1 | h1
  · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) (h.edge_ne x)
  · exact h1

/-- Cubic hypermaps have three-dart nodes. -/
theorem Cubic.node_node_node (h : G.Cubic) (x : D) :
    G.node (G.node (G.node x)) = x := h.1 x (Set.mem_univ x)

/-- Cubic hypermaps have no fixed dart for `node`. -/
theorem Cubic.node_ne (h : G.Cubic) (x : D) : G.node x ≠ x := h.2 x (Set.mem_univ x)

/-- In a cubic hypermap `node (node x) = face (edge x)`. -/
theorem Cubic.node_node (h : G.Cubic) (x : D) :
    G.node (G.node x) = G.face (G.edge x) := by
  conv_lhs => rw [← G.edgeK x]
  exact h.node_node_node (G.face (G.edge x))

/-- The node permutation of a cubic hypermap has order three. -/
theorem Cubic.node_pow_three (h : G.Cubic) : G.node ^ 3 = 1 :=
  (pow_three_eq_one_iff G.node).mpr h.node_node_node

/-- The node orbit of a dart of a cubic hypermap. -/
theorem Cubic.cnode_iff [Finite D] (h : G.Cubic) {x y : D} :
    G.CNode x y ↔ y = x ∨ y = G.node x ∨ y = G.node (G.node x) := by
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    have key : ∀ m : ℕ, (G.node ^ m) x = x ∨ (G.node ^ m) x = G.node x ∨
        (G.node ^ m) x = G.node (G.node x) := by
      intro m
      induction m with
      | zero => exact Or.inl (by simp)
      | succ m ih =>
        rcases ih with hm | hm | hm
        · exact Or.inr (Or.inl (by rw [pow_succ', Perm.mul_apply, hm]))
        · exact Or.inr (Or.inr (by rw [pow_succ', Perm.mul_apply, hm]))
        · exact Or.inl (by rw [pow_succ', Perm.mul_apply, hm, h.node_node_node])
    rcases key n with hk | hk | hk
    exacts [Or.inl (by rw [← hn, hk]), Or.inr (Or.inl (by rw [← hn, hk])),
      Or.inr (Or.inr (by rw [← hn, hk]))]
  · rintro (rfl | rfl | rfl)
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
    · exact sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl _ _))

/-- Nodes of a cubic hypermap have exactly three darts. -/
theorem Cubic.minimalPeriod_node (h : G.Cubic) (x : D) :
    Function.minimalPeriod G.node x = 3 := by
  have h3 : Function.IsPeriodicPt (G.node : D → D) 3 x := by
    change G.node (G.node (G.node x)) = x
    exact h.node_node_node x
  rcases (Nat.dvd_prime Nat.prime_three).mp h3.minimalPeriod_dvd with h1 | h1
  · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) (h.node_ne x)
  · exact h1

/-- A cubic hypermap is precubic. -/
theorem Cubic.precubic (h : G.Cubic) : G.Precubic := fun x => (h.minimalPeriod_node x).le

/-- Quasicubic hypermaps have three-dart nodes away from `r`. -/
theorem Quasicubic.node_node_node {r : List D} (h : G.Quasicubic r) {x : D} (hx : x ∉ r) :
    G.node (G.node (G.node x)) = x := h.1 x hx

/-- Quasicubic hypermaps have no fixed dart for `node` away from `r`. -/
theorem Quasicubic.node_ne {r : List D} (h : G.Quasicubic r) {x : D} (hx : x ∉ r) :
    G.node x ≠ x := h.2 x hx

/-- A cubic hypermap is quasicubic for any list of darts. -/
theorem Cubic.quasicubic (h : G.Cubic) (r : List D) : G.Quasicubic r :=
  ⟨fun x _ => h.node_node_node x, fun x _ => h.node_ne x⟩

/-- Being quasicubic for an empty perimeter is being cubic. -/
theorem quasicubic_nil_iff : G.Quasicubic [] ↔ G.Cubic :=
  ⟨fun h => ⟨fun x _ => h.1 x (by simp), fun x _ => h.2 x (by simp)⟩,
   fun h => h.quasicubic []⟩

end SpecialMaps

/-! #### The special geometries under the derived hypermaps -/

/-- Dualising preserves plainness. -/
theorem plain_dual (G : Hypermap D) : G.dual.Plain ↔ G.Plain := by
  rw [plain_iff, plain_iff, dual_edge]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x => ?_, (inv_ne_iff G.edge).mp h₂⟩
    have hx := h₁ (G.edge (G.edge x))
    simpa using hx.symm
  · rintro ⟨h₁, h₂⟩
    have hinv : (G.edge⁻¹ : Perm D) = G.edge :=
      inv_eq_of_mul_eq_one_right ((pow_two_eq_one_iff G.edge).mpr h₁ ▸ (pow_two G.edge).symm)
    rw [hinv]
    exact ⟨h₁, h₂⟩

/-- Mirroring preserves plainness. -/
theorem plain_mirror (G : Hypermap D) : G.mirror.Plain ↔ G.Plain := by
  have key : ∀ H : Hypermap D, H.Plain → H.mirror.Plain := by
    intro H h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · change H.face (H.node (H.face (H.node x))) = x
      rw [h.node_face, H.nodeK]
    · change H.face (H.node x) ≠ x
      intro hx
      have h2 : H.face (H.edge (H.node x)) = H.face (H.node x) := by rw [H.nodeK, hx]
      exact h.edge_ne (H.node x) (H.face.injective h2)
  refine ⟨fun h => ?_, key G⟩
  have hm := key G.mirror h
  rwa [mirror_mirror] at hm

/-- Mirroring preserves cubicity. -/
theorem cubic_mirror (G : Hypermap D) : G.mirror.Cubic ↔ G.Cubic := by
  rw [cubic_iff, cubic_iff, mirror_node, ← pow_three_eq_one_iff, ← pow_three_eq_one_iff,
    inv_pow, inv_eq_one, inv_ne_iff]

/-- Mirroring preserves precubicity. -/
theorem precubic_mirror (G : Hypermap D) : G.mirror.Precubic ↔ G.Precubic := by
  constructor <;> intro h x
  · have hx := h x
    rwa [mirror_node, minimalPeriod_inv] at hx
  · have hx := h x
    rwa [mirror_node, minimalPeriod_inv]

/-! ### The Euler formula for plain cubic hypermaps -/

section EulerFormula

variable [Finite D]

/-- If a permutation without fixed points satisfies `f ^ k = 1` for a prime `k`,
then all of its orbits have `k` darts, so the dart count is `k` times the orbit
count. -/
theorem card_eq_mul_cycleCount {f : Perm D} {k : ℕ} (hk : k.Prime) (hpow : f ^ k = 1)
    (hfix : ∀ x : D, f x ≠ x) : Nat.card D = k * cycleCount f := by
  classical
  have _ : Fintype D := Fintype.ofFinite D
  have hsupp : f.support = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun x => Perm.mem_support.mpr (hfix x)
  have hmem : ∀ n ∈ f.cycleType, n = k := by
    intro n hn
    have hdvd : n ∣ k := (Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hpow)
    rcases (Nat.dvd_prime hk).mp hdvd with h | h
    · have h2 := Perm.two_le_of_mem_cycleType hn
      omega
    · exact h
  have hrep : f.cycleType = Multiset.replicate (Multiset.card f.cycleType) k :=
    Multiset.eq_replicate_card.mpr hmem
  have hsum : f.cycleType.sum = Multiset.card f.cycleType * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
  have hcard : f.cycleType.sum = Fintype.card D := by
    rw [Perm.sum_cycleType, hsupp, Finset.card_univ]
  have hcount : cycleCount f = Multiset.card f.cycleType := by
    rw [cycleCount_eq', hcard, Nat.sub_self, Nat.zero_add]
  rw [Nat.card_eq_fintype_card, hcount, ← hcard, hsum]
  exact Nat.mul_comm _ _

/-- A plain hypermap has twice as many darts as edges. -/
theorem Plain.card_eq {G : Hypermap D} (h : G.Plain) :
    Nat.card D = 2 * cycleCount G.edge :=
  card_eq_mul_cycleCount Nat.prime_two h.edge_pow_two h.edge_ne

/-- A cubic hypermap has three times as many darts as nodes. -/
theorem Cubic.card_eq {G : Hypermap D} (h : G.Cubic) :
    Nat.card D = 3 * cycleCount G.node :=
  card_eq_mul_cycleCount Nat.prime_three h.node_pow_three h.node_ne

/-- **The Euler formula for plain cubic connected hypermaps**: such a hypermap
is planar exactly when six times its number of faces is its number of darts plus
twelve. -/
theorem cubic_Euler {G : Hypermap D} (hp : G.Plain) (hc : G.Cubic) (hconn : G.Connected) :
    G.Planar ↔ 6 * cycleCount G.face = Nat.card D + 12 := by
  have _ : Fintype D := Fintype.ofFinite D
  have hcc : G.compCount = 1 := hconn
  have heven := G.evenGenus
  simp only [EvenGenus, EulerLhs, EulerRhs] at heven
  rw [hcc] at heven
  have hE := hp.card_eq
  have hN := hc.card_eq
  simp only [Planar]
  omega

end EulerFormula

/-! ### Adjacency -/

section Adj

variable (G : Hypermap D)

/-- The ring link relation: `y` lies in the face of `edge x`. -/
def Rlink (x y : D) : Prop := G.CFace (G.edge x) y

/-- `x` and `y` lie in adjacent faces: some dart in the face of `x` is
`Rlink`ed to `y`. -/
def Adj (x y : D) : Prop := ∃ z, G.CFace x z ∧ G.Rlink z y

/-- `r` is chordless: darts of `r` in adjacent faces are cyclically
consecutive. -/
def Chordless (r : List D) : Prop :=
  ∀ x ∈ r, ∀ y ∈ r, G.Adj x y → y = x ∨ CyclicNext r x y ∨ CyclicNext r y x

/-- `A` is R-path connected: any two of its darts are joined by an `Rlink` path
inside `A`. -/
def RlinkConnected (A : Set D) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∃ p : List D,
    List.IsChain G.Rlink (G.node (G.face x) :: (p ++ [y])) ∧ ∀ z ∈ p, z ∈ A

variable {G}

/-- A dart is `Rlink`ed to its edge. -/
theorem rlink_edge (x : D) : G.Rlink x (G.edge x) := SameCycle.refl _ _

/-- `Rlink` only depends on the face of its second argument. -/
theorem rlink_congr_right {y₁ y₂ : D} (h : G.CFace y₁ y₂) (x : D) :
    G.Rlink x y₁ ↔ G.Rlink x y₂ :=
  ⟨fun hx => hx.trans h, fun hx => hx.trans h.symm⟩

/-- Auxiliary induction on a bound for the length of the path. -/
private theorem exists_simple_rlink_aux :
    ∀ (n : ℕ) (x : D) (p : List D), p.length ≤ n → List.IsChain G.Rlink (x :: p) →
      ∃ q : List D, List.IsChain G.Rlink (x :: q) ∧ G.Simple q ∧
        (x :: q).getLast? = (x :: p).getLast? ∧ (q = [] ↔ p = []) ∧ ∀ z ∈ q, z ∈ p := by
  intro n
  induction n with
  | zero =>
    intro x p hlen _
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hp
    exact ⟨[], List.isChain_singleton x, simple_nil, rfl, Iff.rfl, by simp⟩
  | succ n ih =>
    intro x p hlen hchain
    cases p with
    | nil => exact ⟨[], List.isChain_singleton x, simple_nil, rfl, Iff.rfl, by simp⟩
    | cons y p =>
      obtain ⟨hxy, hchain'⟩ := List.isChain_cons_cons.mp hchain
      by_cases hb : G.Fband p y
      · obtain ⟨z, hz, hyz⟩ := hb
        obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hz
        have hzchain : List.IsChain G.Rlink (z :: p₂) := by
          have hc : List.IsChain G.Rlink ((y :: p₁) ++ z :: p₂) := by
            simpa using hchain'
          exact (List.isChain_split.mp hc).2
        have hxz : G.Rlink x z := (rlink_congr_right hyz x).mp hxy
        have hlen2 : (z :: p₂).length ≤ n := by
          simp only [List.length_cons, List.length_append] at hlen ⊢
          omega
        obtain ⟨q, hqchain, hqsimple, hqlast, hqnil, hqsub⟩ :=
          ih x (z :: p₂) hlen2 (List.isChain_cons_cons.mpr ⟨hxz, hzchain⟩)
        have hlast : (y :: (p₁ ++ z :: p₂)).getLast? = (z :: p₂).getLast? := by
          rw [show y :: (p₁ ++ z :: p₂) = (y :: p₁) ++ (z :: p₂) from rfl,
            List.getLast?_append, List.getLast?_eq_some_getLast (List.cons_ne_nil z p₂),
            Option.some_or]
        refine ⟨q, hqchain, hqsimple, ?_, ?_, ?_⟩
        · rw [hqlast, List.getLast?_cons_cons, List.getLast?_cons_cons, hlast]
        · constructor
          · intro hq
            rw [hqnil] at hq
            simp at hq
          · intro h0
            simp at h0
        · intro w hw
          have hw' := hqsub w hw
          simp only [List.mem_cons, List.mem_append] at hw' ⊢
          tauto
      · have hlen' : p.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨q, hqchain, hqsimple, hqlast, hqnil, hqsub⟩ := ih y p hlen' hchain'
        refine ⟨y :: q, List.isChain_cons_cons.mpr ⟨hxy, hqchain⟩, ?_, ?_, ?_, ?_⟩
        · refine simple_cons.mpr ⟨?_, hqsimple⟩
          rintro ⟨w, hw, hyw⟩
          exact hb ⟨w, hqsub w hw, hyw⟩
        · rw [List.getLast?_cons_cons, List.getLast?_cons_cons]
          exact hqlast
        · simp
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hqsub w hw')

/-- **Path simplification**: every `Rlink` path can be replaced by a face-simple
one with the same endpoints, using only darts of the original path.  This is the
reference's `simplify_rlink`. -/
theorem exists_simple_rlink {x : D} {p : List D} (h : List.IsChain G.Rlink (x :: p)) :
    ∃ q : List D, List.IsChain G.Rlink (x :: q) ∧ G.Simple q ∧
      (x :: q).getLast? = (x :: p).getLast? ∧ (q = [] ↔ p = []) ∧ ∀ z ∈ q, z ∈ p :=
  exists_simple_rlink_aux p.length x p le_rfl h

/-- An `Rlink` is an adjacency. -/
theorem Rlink.adj {x y : D} (h : G.Rlink x y) : G.Adj x y := ⟨x, SameCycle.refl _ _, h⟩

/-- A dart is adjacent to its edge. -/
theorem adj_edge (x : D) : G.Adj x (G.edge x) := (rlink_edge x).adj

/-- Adjacency only depends on the face of its first argument. -/
theorem adj_congr_left {x₁ x₂ : D} (h : G.CFace x₁ x₂) (y : D) : G.Adj x₁ y ↔ G.Adj x₂ y :=
  ⟨fun ⟨z, hz, hzy⟩ => ⟨z, h.symm.trans hz, hzy⟩, fun ⟨z, hz, hzy⟩ => ⟨z, h.trans hz, hzy⟩⟩

/-- Adjacency only depends on the face of its second argument. -/
theorem adj_congr_right {y₁ y₂ : D} (h : G.CFace y₁ y₂) (x : D) : G.Adj x y₁ ↔ G.Adj x y₂ :=
  ⟨fun ⟨z, hz, hzy⟩ => ⟨z, hz, hzy.trans h⟩, fun ⟨z, hz, hzy⟩ => ⟨z, hz, hzy.trans h.symm⟩⟩

/-- Adjacency is invariant under `face` on the left. -/
theorem adj_face_left (x y : D) : G.Adj x y ↔ G.Adj (G.face x) y :=
  adj_congr_left (sameCycle_apply_right.mpr (SameCycle.refl G.face x)) y

/-- Adjacency is invariant under `face` on the right. -/
theorem adj_face_right (x y : D) : G.Adj x y ↔ G.Adj x (G.face y) :=
  adj_congr_right (sameCycle_apply_right.mpr (SameCycle.refl G.face y)) x

/-- A dart is adjacent to its node. -/
theorem adj_node (x : D) : G.Adj (G.node x) x :=
  ⟨G.node x, SameCycle.refl _ _,
    sameCycle_apply_left.mp (by rw [G.nodeK])⟩

/-- In a plain hypermap adjacency is symmetric. -/
theorem Plain.adj_symm (h : G.Plain) {x y : D} (hxy : G.Adj x y) : G.Adj y x := by
  obtain ⟨z, hxz, hzy⟩ := hxy
  exact ⟨G.edge z, hzy.symm, by rw [Rlink, h.edge_edge]; exact hxz.symm⟩

/-- A dart not adjacent to `y₁` but adjacent to `y₂` separates their faces. -/
theorem not_cface_of_not_adj {x y₁ y₂ : D} (h₁ : ¬ G.Adj x y₁) (h₂ : G.Adj x y₂) :
    ¬ G.CFace y₁ y₂ := fun h => h₁ ((adj_congr_right h x).mpr h₂)

/-- In a bridgeless hypermap adjacent darts lie in distinct faces. -/
theorem Bridgeless.not_cface_of_adj (h : G.Bridgeless) {x y : D} (hxy : G.Adj x y) :
    ¬ G.CFace x y := by
  obtain ⟨z, hxz, hzy⟩ := hxy
  intro hxy
  exact h z ((hxz.symm.trans hxy).trans hzy.symm)

/-- Chordlessness is invariant under rotation. -/
theorem chordless_rotate {r : List D} {n : ℕ} : G.Chordless (r.rotate n) ↔ G.Chordless r := by
  simp only [Chordless, List.mem_rotate, cyclicNext_rotate]

end Adj

/-! ### Edge closure of a list of darts -/

section InsertE

variable (G : Hypermap D)

/-- The edge closure of a list of darts: `[x₁, edge x₁, …, xₙ, edge xₙ]`. -/
def insertE (G : Hypermap D) : List D → List D
  | [] => []
  | x :: p => x :: G.edge x :: insertE G p

/-- The edge closure of the empty list is empty. -/
@[simp] theorem insertE_nil : G.insertE [] = [] := rfl

/-- The edge closure of a list with a head. -/
@[simp] theorem insertE_cons (x : D) (p : List D) :
    G.insertE (x :: p) = x :: G.edge x :: G.insertE p := rfl

variable {G}

/-- The edge closure of a list is twice as long. -/
@[simp] theorem length_insertE (p : List D) : (G.insertE p).length = 2 * p.length := by
  induction p with
  | nil => simp
  | cons x p ih => simp only [insertE_cons, List.length_cons, ih]; omega

/-- The edge closure of a concatenation. -/
@[simp] theorem insertE_append (p q : List D) :
    G.insertE (p ++ q) = G.insertE p ++ G.insertE q := by
  induction p with
  | nil => simp
  | cons x p ih => simp [ih]

/-- In a plain hypermap the edge closure of `p` consists of the darts of the
edges met by `p`. -/
theorem mem_insertE [Finite D] (h : G.Plain) {p : List D} {x : D} :
    x ∈ G.insertE p ↔ ∃ y ∈ p, G.CEdge x y := by
  induction p with
  | nil => simp
  | cons y p ih =>
    rw [insertE_cons, List.mem_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨z, hz, hxz⟩)
      · exact ⟨x, by simp, SameCycle.refl _ _⟩
      · exact ⟨y, by simp, sameCycle_apply_left.mpr (SameCycle.refl _ _)⟩
      · exact ⟨z, by simp [hz], hxz⟩
    · rintro ⟨z, hz, hxz⟩
      rcases List.mem_cons.mp hz with hzy | hz'
      · subst hzy
        rcases h.cedge_iff.mp hxz with hx | hx
        · exact Or.inl hx.symm
        · exact Or.inr (Or.inl (by rw [hx, h.edge_edge]))
      · exact Or.inr (Or.inr ⟨z, hz', hxz⟩)

/-- The edge closure of a rotated list is the rotation of its edge closure by
twice as many steps. -/
theorem insertE_rotate :
    ∀ (n : ℕ) (p : List D), G.insertE (p.rotate n) = (G.insertE p).rotate (2 * n) := by
  intro n
  induction n with
  | zero => intro p; simp
  | succ n ih =>
    intro p
    cases p with
    | nil => simp
    | cons x t =>
      have h1 : G.insertE (t ++ [x]) = G.insertE t ++ [x, G.edge x] := by
        rw [insertE_append]
        rfl
      have h3 : (x :: G.edge x :: G.insertE t).rotate 2 = G.insertE t ++ [x, G.edge x] := by
        rw [List.rotate_eq_drop_append_take (by simp)]
        simp
      rw [List.rotate_cons_succ, ih (t ++ [x]), h1, insertE_cons,
        show 2 * (n + 1) = 2 + 2 * n by ring, ← List.rotate_rotate, h3]

end InsertE

/-! ### Bundled geometrical hypotheses

The proof uses various combinations of the geometrical properties above; they
are bundled here under the names of the reference development. -/

section Records

variable (G : Hypermap D)

/-- Planar and bridgeless: the main assumption of the Four Colour Theorem. -/
structure PlanarBridgeless : Prop where
  /-- The hypermap is planar. -/
  planar : G.Planar
  /-- The hypermap is bridgeless. -/
  bridgeless : G.Bridgeless

/-- Plain and cubic; required by the quiz and part developments. -/
structure PlainCubic : Prop where
  /-- The hypermap is plain. -/
  plain : G.Plain
  /-- The hypermap is cubic. -/
  cubic : G.Cubic

/-- Plain, cubic and connected: the hypotheses of the special Euler formula. -/
structure PlainCubicConnected : Prop where
  /-- The hypermap is plain and cubic. -/
  base : G.PlainCubic
  /-- The hypermap is connected. -/
  connected : G.Connected

/-- Planar, plain, cubic and connected; required by the discharge argument. -/
structure PlanarPlainCubicConnected : Prop where
  /-- The hypermap is plain, cubic and connected. -/
  base : G.PlainCubicConnected
  /-- The hypermap is planar. -/
  planar : G.Planar

/-- Plain, cubic and pentagonal; required by the reducibility arguments. -/
structure PlainCubicPentagonal : Prop where
  /-- The hypermap is plain and cubic. -/
  base : G.PlainCubic
  /-- The hypermap is pentagonal. -/
  pentagonal : G.Pentagonal

/-- Planar, bridgeless and plain. -/
structure PlanarBridgelessPlain : Prop where
  /-- The hypermap is planar and bridgeless. -/
  base : G.PlanarBridgeless
  /-- The hypermap is plain. -/
  plain : G.Plain

/-- Planar, bridgeless, plain and connected; required by the snip development. -/
structure PlanarBridgelessPlainConnected : Prop where
  /-- The hypermap is planar, bridgeless and plain. -/
  base : G.PlanarBridgelessPlain
  /-- The hypermap is connected. -/
  connected : G.Connected

/-- Planar, bridgeless, plain and precubic: the inductive assumption of the
proof. -/
structure PlanarBridgelessPlainPrecubic : Prop where
  /-- The hypermap is planar, bridgeless and plain. -/
  base : G.PlanarBridgelessPlain
  /-- The hypermap is precubic. -/
  precubic : G.Precubic

variable (r : List D)

/-- Plain, and cubic away from `r`; required by the quiz development. -/
structure PlainQuasicubic : Prop where
  /-- The hypermap is plain. -/
  plain : G.Plain
  /-- The hypermap is cubic away from `r`. -/
  quasicubic : G.Quasicubic r

/-- Plain and quasicubic, with `r` a duplicate-free N-cycle. -/
structure UcyclePlainQuasicubic : Prop where
  /-- The hypermap is plain and quasicubic for `r`. -/
  base : G.PlainQuasicubic r
  /-- `r` is an N-cycle. -/
  cycle : IsCyclicChain (fun x y => y = G.node x) r
  /-- `r` has no repetitions. -/
  nodup : r.Nodup

/-- A planar map with a duplicate-free N-cycle perimeter; required by the Kempe
development. -/
structure UcyclePlanarPlainQuasicubic : Prop where
  /-- The hypermap is plain and quasicubic, with `r` a duplicate-free N-cycle. -/
  base : G.UcyclePlainQuasicubic r
  /-- The hypermap is planar. -/
  planar : G.Planar

/-- A connected map with a duplicate-free N-cycle perimeter: the hypotheses of
the special Euler formula for configurations. -/
structure UcyclePlainQuasicubicConnected : Prop where
  /-- The hypermap is plain and quasicubic, with `r` a duplicate-free N-cycle. -/
  base : G.UcyclePlainQuasicubic r
  /-- The hypermap is connected. -/
  connected : G.Connected

/-- The full set of geometrical hypotheses on a configuration map, with `r` its
face-simple N-cycle perimeter; required by the embedding development. -/
structure ScyclePlanarBridgelessPlainQuasicubicConnected : Prop where
  /-- The hypermap is plain and quasicubic, connected, with `r` an N-cycle. -/
  base : G.UcyclePlainQuasicubicConnected r
  /-- `r` is face-simple. -/
  simple : G.Simple r
  /-- The hypermap is planar. -/
  planar : G.Planar
  /-- The hypermap is bridgeless. -/
  bridgeless : G.Bridgeless

variable {G r}

/-- The perimeter of a configuration map is a face-simple N-cycle. -/
theorem ScyclePlanarBridgelessPlainQuasicubicConnected.scycle
    (h : G.ScyclePlanarBridgelessPlainQuasicubicConnected r) :
    G.Scycle (fun x y => y = G.node x) r := ⟨h.base.base.cycle, h.simple⟩

/-- A configuration map is planar, bridgeless, plain and connected. -/
theorem ScyclePlanarBridgelessPlainQuasicubicConnected.planarBridgelessPlainConnected
    (h : G.ScyclePlanarBridgelessPlainQuasicubicConnected r) :
    G.PlanarBridgelessPlainConnected :=
  ⟨⟨⟨h.planar, h.bridgeless⟩, h.base.base.base.plain⟩, h.base.connected⟩

end Records

/-! ### The Euler formula for configuration maps

A quasicubic map with a duplicate-free N-cycle perimeter `r` splits into `r`,
which is a single node orbit, and its complement, on which the map is cubic. -/

section QuasicubicEuler

variable [Finite D] {G : Hypermap D} {r : List D}

/-- The node permutation restricted to the darts outside the N-cycle `r`. -/
def nodeOff (G : Hypermap D) {r : List D}
    (hcyc : IsCyclicChain (fun u v => v = G.node u) r) : Perm {x : D // x ∉ r} :=
  G.node.subtypePerm fun x => not_congr (node_mem_iff_mem hcyc x)

/-- The restricted node permutation acts as `node`. -/
@[simp] theorem nodeOff_apply (hcyc : IsCyclicChain (fun u v => v = G.node u) r)
    (u : {x : D // x ∉ r}) : ((G.nodeOff hcyc u : {x : D // x ∉ r}) : D) = G.node (u : D) := rfl

/-- Away from its perimeter a quasicubic map is cubic, so the darts outside the
perimeter are three times as many as the node orbits they form. -/
theorem Quasicubic.card_compl (hq : G.Quasicubic r)
    (hcyc : IsCyclicChain (fun u v => v = G.node u) r) :
    Nat.card {x : D // x ∉ r} = 3 * cycleCount (G.nodeOff hcyc) := by
  refine card_eq_mul_cycleCount Nat.prime_three ((pow_three_eq_one_iff _).mpr fun u => ?_)
    fun u hu => ?_
  · exact Subtype.ext (hq.node_node_node u.property)
  · exact hq.node_ne u.property (congrArg Subtype.val hu)

/-- The node orbits of `G` are its perimeter `r` together with the node orbits
of the darts outside `r`. -/
theorem cycleCount_node_eq (hcyc : IsCyclicChain (fun u v => v = G.node u) r) (hr : r ≠ []) :
    cycleCount G.node = cycleCount (G.nodeOff hcyc) + 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : D, x₀ ∈ r := by
    cases r with
    | nil => exact absurd rfl hr
    | cons a t => exact ⟨a, List.mem_cons_self ..⟩
  have hlift : ∀ u v : {x : D // x ∉ r}, (SameCycle.setoid (G.nodeOff hcyc)).r u v →
      Quotient.mk (SameCycle.setoid G.node) (u : D)
        = Quotient.mk (SameCycle.setoid G.node) (v : D) :=
    fun _ _ huv => Quotient.sound (Perm.sameCycle_subtypePerm.mp huv)
  set φ : Quotient (SameCycle.setoid (G.nodeOff hcyc)) → Quotient (SameCycle.setoid G.node) :=
    Quotient.lift (fun u : {x : D // x ∉ r} => Quotient.mk (SameCycle.setoid G.node) (u : D))
      hlift with hφ
  set ψ : Option (Quotient (SameCycle.setoid (G.nodeOff hcyc))) →
      Quotient (SameCycle.setoid G.node) :=
    fun o => o.elim (Quotient.mk (SameCycle.setoid G.node) x₀) φ with hψ
  have hne : ∀ u : {x : D // x ∉ r}, Quotient.mk (SameCycle.setoid G.node) x₀
      ≠ Quotient.mk (SameCycle.setoid G.node) (u : D) := by
    intro u hu
    exact u.property ((cnode_iff_mem hcyc hx₀ (u : D)).mp (Quotient.exact hu))
  have hbij : Function.Bijective ψ := by
    constructor
    · rintro (_ | q₁) (_ | q₂) hq
      · rfl
      · revert hq
        refine Quotient.inductionOn q₂ fun u hq => ?_
        exact absurd hq (hne u)
      · revert hq
        refine Quotient.inductionOn q₁ fun u hq => ?_
        exact absurd hq.symm (hne u)
      · revert hq
        refine Quotient.inductionOn₂ q₁ q₂ fun u v huv => ?_
        exact congrArg some
          (Quotient.sound (Perm.sameCycle_subtypePerm.mpr (Quotient.exact huv)))
    · intro q
      refine Quotient.inductionOn q fun x => ?_
      by_cases hx : x ∈ r
      · exact ⟨none, Quotient.sound ((cnode_iff_mem hcyc hx₀ x).mpr hx)⟩
      · exact ⟨some (Quotient.mk (SameCycle.setoid (G.nodeOff hcyc)) ⟨x, hx⟩), rfl⟩
  have hcard := Nat.card_eq_of_bijective ψ hbij
  simp only [cycleCount]
  rw [← hcard, Finite.card_option]

/-- The darts of `G` split into a duplicate-free perimeter and its
complement. -/
theorem card_eq_length_add_card_compl (hnodup : r.Nodup) :
    Nat.card D = r.length + Nat.card {x : D // x ∉ r} := by
  classical
  have _ : Fintype D := Fintype.ofFinite D
  have h1 : Nat.card {x : D // x ∈ r} = r.length := by
    have _ : Fintype {x : D // x ∈ r} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun x : D => x ∈ r) = r.toFinset := by
      ext x
      simp
    rw [hfilter, List.toFinset_card_of_nodup hnodup]
  have h2 : Nat.card ({x : D // x ∈ r} ⊕ {x : D // x ∉ r}) = Nat.card D :=
    Nat.card_congr (Equiv.sumCompl fun x : D => x ∈ r)
  rw [← h2, Nat.card_sum, h1]

/-- **The Euler formula for configuration maps**: a plain quasicubic connected
hypermap with a duplicate-free N-cycle perimeter `r` is planar exactly when six
times its number of faces, plus one for the perimeter, is its number of darts
plus twice the perimeter length plus twelve.  The case of an empty perimeter is
`Hypermap.cubic_Euler`. -/
theorem quasicubic_Euler (h : G.UcyclePlainQuasicubicConnected r) (hr : r ≠ []) :
    G.Planar ↔ 6 * (1 + cycleCount G.face) = Nat.card D + (2 * r.length + 12) := by
  have _ : Fintype D := Fintype.ofFinite D
  have hcc : G.compCount = 1 := h.connected
  have heven := G.evenGenus
  simp only [EvenGenus, EulerLhs, EulerRhs] at heven
  rw [hcc] at heven
  have hE := h.base.base.plain.card_eq
  have hcompl := h.base.base.quasicubic.card_compl h.base.cycle
  have hsplit := card_eq_length_add_card_compl (D := D) h.base.nodup
  have hnode := cycleCount_node_eq h.base.cycle hr
  simp only [Planar]
  omega

end QuasicubicEuler

end Hypermap

end FourColor

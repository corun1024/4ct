import Mathlib.Data.List.Chain
import FourColor.Perm

/-!
# Hypermaps

A hypermap is a triple of permutations of a type of *darts* whose composite is
the identity.  This is equivalent to an arbitrary pair of permutations, but the
three-function presentation makes the Euler and genus formulae completely
symmetric in `edge`, `node` and `face`.

The reference development works with MathComp's `finType` functions plus
`cancel` hypotheses, and has to carry injectivity and inverse lemmas by hand.
Here the three maps are `Equiv.Perm`s, so injectivity and inverses come for
free, the defining identity is the single group equation `node * face * edge = 1`,
and the orbit relations `cedge`/`cnode`/`cface` are `Mathlib`'s
`Equiv.Perm.SameCycle`.  Extensional equality of hypermaps (`=m` in the
reference) is then literal equality, so no separate theory is needed.

## Main definitions

* `Hypermap D` — three permutations of `D` with `node * face * edge = 1`.
* `Hypermap.GLink`, `Hypermap.Clink` — the link relations; `Hypermap.Connected`.
* `Hypermap.genus`, `Hypermap.Planar` — the Euler-formula planarity condition.
* `Hypermap.MoebiusPath`, `Hypermap.Jordan` — the Jordan-curve planarity condition.
* `Hypermap.permN`, `permF`, `dual`, `mirror` — the derived hypermaps, all of
  which preserve connectedness and genus.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/hypermap.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D D' : Type*}

/-! ### The equivalence closure of a relation -/

theorem eqvGen_mono {r s : D → D → Prop} (h : ∀ x y, r x y → Relation.EqvGen s x y)
    {x y : D} (hxy : Relation.EqvGen r x y) : Relation.EqvGen s x y := by
  induction hxy with
  | rel x y h' => exact h x y h'
  | refl x => exact Relation.EqvGen.refl x
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem eqvGen_congr {r s : D → D → Prop} (h : ∀ x y, r x y ↔ s x y) (x y : D) :
    Relation.EqvGen r x y ↔ Relation.EqvGen s x y :=
  ⟨eqvGen_mono fun a b hab => Relation.EqvGen.rel a b ((h a b).mp hab),
   eqvGen_mono fun a b hab => Relation.EqvGen.rel a b ((h a b).mpr hab)⟩

theorem eqvGen_flip {r : D → D → Prop} (x y : D) :
    Relation.EqvGen (fun a b => r b a) x y ↔ Relation.EqvGen r x y :=
  ⟨eqvGen_mono fun a b hab => Relation.EqvGen.symm _ _ (Relation.EqvGen.rel b a hab),
   eqvGen_mono fun a b hab => Relation.EqvGen.symm _ _ (Relation.EqvGen.rel b a hab)⟩

/-- `Mem2 p x y` holds when `x` occurs in `p` with `y` at or after it. -/
def Mem2 (p : List D) (x y : D) : Prop :=
  ∃ p₁ p₂, p = p₁ ++ x :: p₂ ∧ (y = x ∨ y ∈ p₂)

namespace Mem2

variable {α β : Type*}

theorem mem_left {p : List α} {a b : α} (h : Mem2 p a b) : a ∈ p := by
  obtain ⟨p₁, p₂, rfl, -⟩ := h
  simp

theorem mem_right {p : List α} {a b : α} (h : Mem2 p a b) : b ∈ p := by
  obtain ⟨p₁, p₂, rfl, hb | hb⟩ := h
  · simp [hb]
  · simp [hb]

theorem cons {x a b : α} {p : List α} (h : Mem2 p a b) : Mem2 (x :: p) a b := by
  obtain ⟨p₁, p₂, rfl, hb⟩ := h
  exact ⟨x :: p₁, p₂, by simp, hb⟩

theorem cons_self {x b : α} {p : List α} (h : b = x ∨ b ∈ p) : Mem2 (x :: p) x b :=
  ⟨[], p, rfl, h⟩

theorem cons_iff {x a b : α} {p : List α} :
    Mem2 (x :: p) a b ↔ (a = x ∧ (b = x ∨ b ∈ p)) ∨ Mem2 p a b := by
  constructor
  · rintro ⟨p₁, p₂, hp, hb⟩
    match p₁ with
    | [] =>
      rw [List.nil_append, List.cons_eq_cons] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact Or.inl ⟨rfl, hb⟩
    | c :: p₁ =>
      rw [List.cons_append, List.cons_eq_cons] at hp
      exact Or.inr ⟨p₁, p₂, hp.2, hb⟩
  · rintro (⟨rfl, hb⟩ | h)
    · exact cons_self hb
    · exact h.cons

/-- Transfer along an injection. -/
theorem map_iff {f : α → β} (hf : Function.Injective f) {l : List α} {a b : α} :
    Mem2 (l.map f) (f a) (f b) ↔ Mem2 l a b := by
  induction l with
  | nil => simp [Mem2]
  | cons c l ih =>
    rw [List.map_cons, cons_iff, cons_iff, ih]
    simp only [hf.eq_iff, List.mem_map, hf.eq_iff]
    constructor
    · rintro (⟨rfl, hb | ⟨w, hw, hwb⟩⟩ | h)
      · exact Or.inl ⟨rfl, Or.inl hb⟩
      · exact Or.inl ⟨rfl, Or.inr (hwb ▸ hw)⟩
      · exact Or.inr h
    · rintro (⟨rfl, hb | hb⟩ | h)
      · exact Or.inl ⟨rfl, Or.inl hb⟩
      · exact Or.inl ⟨rfl, Or.inr ⟨b, hb, rfl⟩⟩
      · exact Or.inr h

end Mem2

/-- A hypermap: three permutations of a type of *darts* whose composite
`node ∘ face ∘ edge` is the identity.  Despite the names, this file develops
only notions symmetric in the three permutations; their geometric reading is
fixed later, in the colouring theory. -/
structure Hypermap (D : Type*) where
  /-- The first permutation. -/
  edge : Perm D
  /-- The second permutation. -/
  node : Perm D
  /-- The third permutation. -/
  face : Perm D
  /-- The defining triangular identity. -/
  node_face_edge : node * face * edge = 1

namespace Hypermap

/-- On a finite dart type three functions satisfying the triangular identity are
automatically permutations, so they define a hypermap.  This is how the derived
maps of the development are built: give the three functions, check the identity,
and the bijectivity comes for free. -/
noncomputable def ofCancel3 [Finite D] (e n f : D → D) (h : ∀ x, n (f (e x)) = x) :
    Hypermap D := by
  have he : Function.Injective e := fun x y hxy => by rw [← h x, ← h y, hxy]
  have hn : Function.Surjective n := fun x => ⟨f (e x), h x⟩
  have he' : Function.Bijective e := ⟨he, Finite.surjective_of_injective he⟩
  have hn' : Function.Bijective n := ⟨Finite.injective_iff_surjective.mpr hn, hn⟩
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := he'.surjective x
    obtain ⟨y', rfl⟩ := he'.surjective y
    have : n (f (e x')) = n (f (e y')) := by rw [hxy]
    rw [h, h] at this
    rw [this]
  have hf' : Function.Bijective f := ⟨hf, Finite.surjective_of_injective hf⟩
  exact
    { edge := Equiv.ofBijective e he'
      node := Equiv.ofBijective n hn'
      face := Equiv.ofBijective f hf'
      node_face_edge := by
        refine Equiv.ext fun x => ?_
        simpa using h x }

@[simp] theorem ofCancel3_edge [Finite D] (e n f : D → D) (h : ∀ x, n (f (e x)) = x)
    (x : D) : (ofCancel3 e n f h).edge x = e x := rfl

@[simp] theorem ofCancel3_node [Finite D] (e n f : D → D) (h : ∀ x, n (f (e x)) = x)
    (x : D) : (ofCancel3 e n f h).node x = n x := rfl

@[simp] theorem ofCancel3_face [Finite D] (e n f : D → D) (h : ∀ x, n (f (e x)) = x)
    (x : D) : (ofCancel3 e n f h).face x = f x := rfl

@[ext] theorem ext {G H : Hypermap D} (he : G.edge = H.edge) (hn : G.node = H.node)
    (hf : G.face = H.face) : G = H := by
  cases G; cases H; simp_all

section Basic

variable (G : Hypermap D)

private theorem mul_rotate_eq_one {α : Type*} [Group α] {a b c : α} (h : a * b * c = 1) :
    b * c * a = 1 := by
  have h' : a * (b * c) = 1 := by rwa [mul_assoc] at h
  rw [← inv_eq_of_mul_eq_one_right h', inv_mul_cancel]

theorem face_edge_node : G.face * G.edge * G.node = 1 :=
  mul_rotate_eq_one G.node_face_edge

theorem edge_node_face : G.edge * G.node * G.face = 1 :=
  mul_rotate_eq_one G.face_edge_node

@[simp] theorem edgeK (x : D) : G.node (G.face (G.edge x)) = x := by
  simpa using congrArg (fun p : Perm D => p x) G.node_face_edge

@[simp] theorem nodeK (x : D) : G.face (G.edge (G.node x)) = x := by
  simpa using congrArg (fun p : Perm D => p x) G.face_edge_node

@[simp] theorem faceK (x : D) : G.edge (G.node (G.face x)) = x := by
  simpa using congrArg (fun p : Perm D => p x) G.edge_node_face

theorem node_mul_face_eq_edge_inv : G.node * G.face = G.edge⁻¹ := by
  have h : G.edge * (G.node * G.face) = 1 := by rw [← mul_assoc]; exact G.edge_node_face
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- Darts on a common edge orbit. -/
abbrev CEdge : D → D → Prop := G.edge.SameCycle

/-- Darts on a common node orbit. -/
abbrev CNode : D → D → Prop := G.node.SameCycle

/-- Darts on a common face orbit. -/
abbrev CFace : D → D → Prop := G.face.SameCycle

end Basic

/-! ### Link relations and components -/

section Links

variable (G : Hypermap D)

/-- `y` is the image of `x` under one of the three permutations. -/
def GLink (x y : D) : Prop := y = G.edge x ∨ y = G.node x ∨ y = G.face x

/-- The contour link: either a reverse N-link or an F-link. -/
def Clink (x y : D) : Prop := x = G.node y ∨ G.face x = y

theorem cedge_edge (x : D) : G.CEdge x (G.edge x) := ⟨1, by simp⟩
theorem cnode_node (x : D) : G.CNode x (G.node x) := ⟨1, by simp⟩
theorem cface_face (x : D) : G.CFace x (G.face x) := ⟨1, by simp⟩

theorem glink_edge (x : D) : G.GLink x (G.edge x) := Or.inl rfl
theorem glink_node (x : D) : G.GLink x (G.node x) := Or.inr (Or.inl rfl)
theorem glink_face (x : D) : G.GLink x (G.face x) := Or.inr (Or.inr rfl)

theorem clink_node (x : D) : G.Clink (G.node x) x := Or.inl rfl
theorem clink_face (x : D) : G.Clink x (G.face x) := Or.inr rfl

end Links

section Components

variable (G : Hypermap D)

/-- Darts in the same component of `G`. -/
def gcompSetoid : Setoid D :=
  ⟨Relation.EqvGen G.GLink, Relation.EqvGen.is_equivalence _⟩

/-- The number of components of `G`. -/
noncomputable def compCount : ℕ := Nat.card (Quotient G.gcompSetoid)

/-- A hypermap is connected when it has exactly one component. -/
def Connected : Prop := G.compCount = 1

/-- Contour paths generate the same components as the three permutations. -/
theorem eqvGen_clink_iff_glink (x y : D) :
    Relation.EqvGen G.Clink x y ↔ Relation.EqvGen G.GLink x y := by
  constructor
  · refine eqvGen_mono fun a b hab => ?_
    rcases hab with h | h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel b a (Or.inr (Or.inl h)))
    · exact Relation.EqvGen.rel a b (Or.inr (Or.inr h.symm))
  · refine eqvGen_mono fun a b hab => ?_
    rcases hab with h | h | h
    · -- an E-link is a reverse N-link followed by an F-link through `face (edge a)`
      have h₁ : G.Clink a (G.face (G.edge a)) := Or.inl (G.edgeK a).symm
      have h₂ : G.Clink b (G.face (G.edge a)) := Or.inr (by rw [h])
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h₁)
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h₂))
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel b a (Or.inl h))
    · exact Relation.EqvGen.rel a b (Or.inr h.symm)

/-- Darts on a common edge orbit are in the same component. -/
theorem eqvGen_glink_of_sameCycle_edge [Finite D] {x y : D} (h : G.edge.SameCycle x y) :
    Relation.EqvGen G.GLink x y := by
  rw [sameCycle_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | @tail b c _ hbc ih =>
    exact Relation.EqvGen.trans _ _ _ ih
      (Relation.EqvGen.rel _ _ (show G.GLink b c by rw [hbc]; exact G.glink_edge b))

end Components

/-! ### Euler formula, genus and planarity -/

section Genus

variable (G : Hypermap D)

/-- Left-hand side of the hypermap Euler formula. -/
noncomputable def EulerLhs : ℕ := 2 * G.compCount + Nat.card D

/-- Right-hand side of the hypermap Euler formula. -/
noncomputable def EulerRhs : ℕ :=
  cycleCount G.edge + (cycleCount G.node + cycleCount G.face)

/-- The genus of a hypermap: the least number of holes of an oriented manifold
it embeds in. -/
noncomputable def genus : ℕ := (G.EulerLhs - G.EulerRhs) / 2

/-- The genus formula is exact, i.e. the subtraction in `genus` does not
truncate.  This holds for every hypermap; it is proved in the Jordan-curve
development. -/
def EvenGenus : Prop := G.EulerLhs = 2 * G.genus + G.EulerRhs

/-- The Euler-formula planarity condition. -/
def Planar : Prop := G.genus = 0

end Genus

/-! ### Contour connectivity

On a finite dart type every link is reversible by a path of links in the same
direction, because a permutation of a finite type has finite order.  Hence
contour reachability is symmetric, and in a connected hypermap any dart is
joined to any other by a contour path. -/

section FiniteConnectivity

variable [Finite D]

variable (G : Hypermap D)

/-- Every contour link can be reversed by a contour path. -/
theorem clink_symm {x y : D} (h : G.Clink x y) : Relation.ReflTransGen G.Clink y x := by
  rcases h with h | h
  · subst h
    have hstep : ∀ a b : D, b = G.node⁻¹ a → G.Clink a b := by
      rintro a b rfl; exact Or.inl (by simp)
    have hpath := reflTransGen_perm_inv (G.node⁻¹) y
    simp only [inv_inv] at hpath
    exact Relation.ReflTransGen.mono hstep _ _ hpath
  · subst h
    have hstep : ∀ a b : D, b = G.face a → G.Clink a b := by
      rintro a b rfl; exact Or.inr rfl
    have hpath := reflTransGen_perm_inv G.face (G.face x)
    have hx : G.face⁻¹ (G.face x) = x := by simp
    rw [hx] at hpath
    exact Relation.ReflTransGen.mono hstep _ _ hpath

theorem reflTransGen_clink_symm {x y : D} (h : Relation.ReflTransGen G.Clink x y) :
    Relation.ReflTransGen G.Clink y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (G.clink_symm hbc).trans ih

theorem reflTransGen_clink_of_eqvGen {x y : D} (h : Relation.EqvGen G.Clink x y) :
    Relation.ReflTransGen G.Clink x y := by
  induction h with
  | rel a b hab => exact Relation.ReflTransGen.single hab
  | refl a => exact Relation.ReflTransGen.refl
  | symm a b _ ih => exact G.reflTransGen_clink_symm ih
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- In a connected hypermap any dart is joined to any other by a contour path. -/
theorem connected_clink (h : G.Connected) (x y : D) :
    Relation.ReflTransGen G.Clink x y := by
  have hsub : Subsingleton (Quotient G.gcompSetoid) := (Nat.card_eq_one_iff_unique.mp h).1
  have : (Quotient.mk G.gcompSetoid x) = Quotient.mk G.gcompSetoid y := Subsingleton.elim _ _
  exact G.reflTransGen_clink_of_eqvGen
    ((G.eqvGen_clink_iff_glink x y).mpr (Quotient.exact this))

/-- The list form of `connected_clink`. -/
theorem connected_clink_list (h : G.Connected) (x y : D) :
    ∃ p : List D, List.IsChain G.Clink (x :: p) ∧
      (x :: p).getLast (List.cons_ne_nil _ _) = y :=
  List.exists_isChain_cons_of_relationReflTransGen (G.connected_clink h x y)

end FiniteConnectivity

/-! ### The Jordan planarity condition -/

section Jordan

variable (G : Hypermap D)

/-- A Moebius path: a nontrivial duplicate-free contour path carrying two
crossing N-links.  In a planar hypermap N-links and F-links leave a contour on
opposite sides, so such a path can only be embedded in a Moebius strip or a
surface of higher genus. -/
def MoebiusPath : List D → Prop
  | [] => False
  | x :: p =>
    (x :: p).Nodup ∧ List.IsChain G.Clink (x :: p) ∧
      Mem2 p (G.node⁻¹ (p.getLastD x)) (G.node x)

/-- The Moebius condition with the crossing dart named: `t` is the dart whose
`node` image ends the path.  This is the form in which Moebius paths are
transported between a hypermap and its Walkup transforms, where the `node`
permutation changes. -/
def MoebiusData (x : D) (p : List D) (t : D) : Prop :=
  (x :: p).Nodup ∧ List.IsChain G.Clink (x :: p) ∧ G.node t = p.getLastD x ∧
    Mem2 p t (G.node x)

theorem moebiusPath_of_data {x t : D} {p : List D} (h : G.MoebiusData x p t) :
    G.MoebiusPath (x :: p) := by
  obtain ⟨hu, hc, hn, hm⟩ := h
  refine ⟨hu, hc, ?_⟩
  have ht : G.node⁻¹ (p.getLastD x) = t := by rw [← hn]; simp
  rwa [ht]

/-- The Jordan-curve planarity condition: no Moebius paths. -/
def Jordan : Prop := ∀ q, ¬ G.MoebiusPath q

end Jordan

/-! ### Derived hypermaps -/

section Derived

variable (G : Hypermap D)

/-- Rotate the three permutations left: `edge ↦ node`. -/
def permN : Hypermap D := ⟨G.node, G.face, G.edge, G.face_edge_node⟩

/-- Rotate the three permutations right: `edge ↦ face`. -/
def permF : Hypermap D := ⟨G.face, G.edge, G.node, G.edge_node_face⟩

/-- The dual hypermap: invert all three permutations and transpose node and face. -/
def dual : Hypermap D :=
  ⟨G.edge⁻¹, G.face⁻¹, G.node⁻¹, by
    rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, G.edge_node_face, inv_one]⟩

/-- The mirror hypermap: invert node and face in place, and garble edge. -/
def mirror : Hypermap D :=
  ⟨G.face * G.node, G.node⁻¹, G.face⁻¹, by
    simp [mul_assoc]⟩

@[simp] theorem permN_edge : G.permN.edge = G.node := rfl
@[simp] theorem permN_node : G.permN.node = G.face := rfl
@[simp] theorem permN_face : G.permN.face = G.edge := rfl
@[simp] theorem permF_edge : G.permF.edge = G.face := rfl
@[simp] theorem permF_node : G.permF.node = G.edge := rfl
@[simp] theorem permF_face : G.permF.face = G.node := rfl
@[simp] theorem dual_edge : G.dual.edge = G.edge⁻¹ := rfl
@[simp] theorem dual_node : G.dual.node = G.face⁻¹ := rfl
@[simp] theorem dual_face : G.dual.face = G.node⁻¹ := rfl
@[simp] theorem mirror_edge : G.mirror.edge = G.face * G.node := rfl
@[simp] theorem mirror_node : G.mirror.node = G.node⁻¹ := rfl
@[simp] theorem mirror_face : G.mirror.face = G.face⁻¹ := rfl

@[simp] theorem dual_dual : G.dual.dual = G := by
  refine ext ?_ ?_ ?_
  · change G.dual.edge⁻¹ = G.edge; rw [dual_edge, inv_inv]
  · change G.dual.face⁻¹ = G.node; rw [dual_face, inv_inv]
  · change G.dual.node⁻¹ = G.face; rw [dual_node, inv_inv]

@[simp] theorem mirror_mirror : G.mirror.mirror = G := by
  refine ext ?_ ?_ ?_
  · change G.mirror.face * G.mirror.node = G.edge
    rw [mirror_face, mirror_node, ← mul_inv_rev, G.node_mul_face_eq_edge_inv, inv_inv]
  · change G.mirror.node⁻¹ = G.node; rw [mirror_node, inv_inv]
  · change G.mirror.face⁻¹ = G.face; rw [mirror_face, inv_inv]

/-! #### Component counts of the derived maps -/

theorem compCount_congr {G : Hypermap D} {H : Hypermap D'} (e : D ≃ D')
    (h : ∀ x y, Relation.EqvGen G.GLink x y ↔ Relation.EqvGen H.GLink (e x) (e y)) :
    G.compCount = H.compCount :=
  Nat.card_congr (Quotient.congr e h)

@[simp] theorem compCount_permN : G.permN.compCount = G.compCount :=
  compCount_congr (Equiv.refl D) fun x y =>
    eqvGen_congr (fun a b => by simp only [GLink, permN_edge, permN_node]; tauto) x y

@[simp] theorem compCount_permF : G.permF.compCount = G.compCount :=
  compCount_congr (Equiv.refl D) fun x y =>
    eqvGen_congr (fun a b => by simp only [GLink, permF_edge, permF_node]; tauto) x y

@[simp] theorem compCount_dual : G.dual.compCount = G.compCount := by
  refine compCount_congr (Equiv.refl D) fun x y => ?_
  refine Iff.trans ?_ (eqvGen_flip (r := G.GLink) x y)
  refine eqvGen_congr (fun a b => ?_) x y
  simp only [GLink, dual_edge, dual_node, dual_face]
  constructor
  · rintro (h | h | h) <;> subst h <;> simp
  · rintro (h | h | h) <;> subst h <;> simp

@[simp] theorem compCount_mirror : G.mirror.compCount = G.compCount := by
  refine compCount_congr (Equiv.refl D) fun x y => ?_
  refine Iff.trans ((G.mirror.eqvGen_clink_iff_glink x y).symm) ?_
  refine Iff.trans ?_ (G.eqvGen_clink_iff_glink x y)
  refine Iff.trans ?_ (eqvGen_flip (r := G.Clink) x y)
  refine eqvGen_congr (fun a b => ?_) x y
  change (a = G.node⁻¹ b ∨ G.face⁻¹ a = b) ↔ (b = G.node a ∨ G.face b = a)
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [← h]; simp)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (by rw [← h]; simp)

/-! #### Genus of the derived maps -/

@[simp] theorem genus_permN : G.permN.genus = G.genus := by
  simp only [genus, EulerLhs, EulerRhs, compCount_permN, permN_edge, permN_node, permN_face]
  ring_nf

@[simp] theorem genus_permF : G.permF.genus = G.genus := by
  simp only [genus, EulerLhs, EulerRhs, compCount_permF, permF_edge, permF_node, permF_face]
  ring_nf

@[simp] theorem genus_dual : G.dual.genus = G.genus := by
  simp only [genus, EulerLhs, EulerRhs, compCount_dual, dual_edge, dual_node, dual_face,
    cycleCount_inv]
  ring_nf

@[simp] theorem genus_mirror : G.mirror.genus = G.genus := by
  have hedge : cycleCount (G.face * G.node) = cycleCount G.edge := by
    rw [cycleCount_mul_comm, G.node_mul_face_eq_edge_inv, cycleCount_inv]
  simp only [genus, EulerLhs, EulerRhs, compCount_mirror, mirror_edge, mirror_node,
    mirror_face, cycleCount_inv, hedge]

@[simp] theorem planar_permN : G.permN.Planar ↔ G.Planar := by simp [Planar]
@[simp] theorem planar_permF : G.permF.Planar ↔ G.Planar := by simp [Planar]
@[simp] theorem planar_dual : G.dual.Planar ↔ G.Planar := by simp [Planar]
@[simp] theorem planar_mirror : G.mirror.Planar ↔ G.Planar := by simp [Planar]

@[simp] theorem connected_permN : G.permN.Connected ↔ G.Connected := by simp [Connected]
@[simp] theorem connected_permF : G.permF.Connected ↔ G.Connected := by simp [Connected]
@[simp] theorem connected_dual : G.dual.Connected ↔ G.Connected := by simp [Connected]
@[simp] theorem connected_mirror : G.mirror.Connected ↔ G.Connected := by simp [Connected]

end Derived

end Hypermap

namespace Hypermap

/-! ### Euler parity

The two sides of the hypermap Euler formula always have the same parity.  The
reference obtains this as a byproduct of the full Walkup induction; it follows
directly from the fact that `Equiv.Perm.sign` is a homomorphism, since the
defining identity of a hypermap says `node * face * edge = 1`.
-/

private theorem neg_one_pow_inj {a b : ℕ} (h : (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b) :
    a % 2 = b % 2 := by
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb
  · rw [Nat.even_iff.mp ha, Nat.even_iff.mp hb]
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h; exact absurd h (by decide)
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h; exact absurd h (by decide)
  · rw [Nat.odd_iff.mp ha, Nat.odd_iff.mp hb]

private theorem units_triple {a b c u : ℤˣ} (hu : u * u = 1) (habc : a * b * c = 1) :
    u * a * (u * b * (u * c)) = u := by
  have h3 : u * a * (u * b * (u * c)) = u * u * u * (a * b * c) := by
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [h3, habc, mul_one, mul_assoc, hu, mul_one]

/-- **Euler parity.**  For every hypermap the two sides of the Euler formula
have the same parity, so the genus is never truncated by an odd difference. -/
theorem eulerLhs_mod_two_eq_eulerRhs_mod_two [Fintype D] [DecidableEq D]
    (G : Hypermap D) : G.EulerLhs % 2 = G.EulerRhs % 2 := by
  have hu : (-1 : ℤˣ) ^ 2 = 1 := by decide
  have hN : Nat.card D = Fintype.card D := Nat.card_eq_fintype_card
  have hu2 : ((-1 : ℤˣ) ^ Fintype.card D) * ((-1 : ℤˣ) ^ Fintype.card D) = 1 := by
    rw [← pow_add]
    exact (Nat.even_iff.mpr (by omega)).neg_one_pow
  have hsign :
      Equiv.Perm.sign G.edge * Equiv.Perm.sign G.node * Equiv.Perm.sign G.face = 1 := by
    have h := congrArg Equiv.Perm.sign G.node_face_edge
    simp only [map_mul, map_one] at h
    calc Equiv.Perm.sign G.edge * Equiv.Perm.sign G.node * Equiv.Perm.sign G.face
        = Equiv.Perm.sign G.node * Equiv.Perm.sign G.face * Equiv.Perm.sign G.edge := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := h
  refine neg_one_pow_inj ?_
  have hlhs : (-1 : ℤˣ) ^ G.EulerLhs = (-1 : ℤˣ) ^ Fintype.card D := by
    rw [EulerLhs, hN, pow_add, pow_mul, hu, one_pow, one_mul]
  have hrhs : (-1 : ℤˣ) ^ G.EulerRhs = (-1 : ℤˣ) ^ Fintype.card D := by
    rw [EulerRhs, pow_add, pow_add, neg_one_pow_cycleCount, neg_one_pow_cycleCount,
      neg_one_pow_cycleCount]
    exact units_triple hu2 hsign
  rw [hlhs, hrhs]

end Hypermap

end FourColor

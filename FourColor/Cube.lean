import FourColor.Geometry
import FourColor.Coloring

/-!
# The cube of a hypermap

Reduction of the colouring problem to plain cubic maps.  This is not an
inductive step, so we are free to build a *larger* map: `G.cube` splits every
dart of `G` into six copies, tagged by `CubeTag`, and the three permutations
are arranged so that the result is plain and cubic, has the same genus and the
same components as `G`, is bridgeless exactly when `G` is, and is
four-colourable only if `G` is.

The six tags fall into three kinds as far as the *faces* of `G.cube` are
concerned: the copies tagged `CubeTag.e` reproduce the edge orbits of `G`, the
copies tagged `CubeTag.fe` reproduce the node orbits, and the remaining four
tags together reproduce each face orbit of `G` (four cube darts per dart of the
face).  So `G.cube` has one face for each edge, node and face of `G`, which is
exactly the right-hand side of the Euler formula for `G`; this is the content
of `Hypermap.cycleCount_cube_face` and the reason the genus is preserved.

The reference development proves these orbit counts with `fun_adjunction`, a
bespoke theory of functions mapping one orbit relation onto another.  Here the
same information is packaged as an explicit `Equiv` between the quotient types
that `FourColor.cycleCount` and `Hypermap.compCount` count, which is both
shorter and closer to what is actually being said.

## Main definitions

* `CubeTag`, `CubeDart` — the six copies of a dart and the dart type of the cube.
* `Hypermap.cubeEdge`, `Hypermap.cubeNode`, `Hypermap.cubeFace` — the three
  permutations of the cube, each with its inverse given explicitly.
* `Hypermap.cube` — the cube of a hypermap.
* `Hypermap.cubeFaceClass` — the invariant classifying the faces of the cube.

## Main results

* `Hypermap.plain_cube`, `Hypermap.cubic_cube` — the cube is plain and cubic.
* `Hypermap.cycleCount_cube_face`, `Hypermap.compCount_cube` — the orbit counts.
* `Hypermap.genus_cube`, `Hypermap.planar_cube`, `Hypermap.connected_cube` —
  the cube has the same genus, planarity and connectivity as its argument.
* `Hypermap.bridgeless_cube` — the cube is bridgeless exactly when `G` is.
* `Hypermap.FourColorable.of_cube` — four-colouring the cube four-colours `G`.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/cube.v` of the Coq development.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {D : Type*}

/-- The tag flagging the six copies of each dart of `G` in `G.cube`.  The names
record how the copy is attached to its original dart: the copy `CTnf` sits at
`node (face _)`, and so on. -/
inductive CubeTag
  | /-- The `node` copy. -/ n
  | /-- The `edge`-`node` copy. -/ en
  | /-- The `face` copy. -/ f
  | /-- The `node`-`face` copy. -/ nf
  | /-- The `edge` copy, which carries the edge orbits of `G`. -/ e
  | /-- The `face`-`edge` copy, which carries the node orbits of `G`. -/ fe
  deriving DecidableEq

namespace CubeTag

instance : Fintype CubeTag :=
  ⟨⟨{n, en, f, nf, e, fe}, by decide⟩, fun t => by cases t <;> decide⟩

/-- There are six copies of each dart. -/
@[simp] theorem card_eq : Fintype.card CubeTag = 6 := rfl

end CubeTag

/-- A dart of the cube: a tagged copy of a dart of the original hypermap. -/
abbrev CubeDart (D : Type*) := CubeTag × D

namespace Hypermap

variable (G : Hypermap D)

/-! ### The three permutations of the cube -/

/-- The edge permutation of the cube, as a function.  It is an involution
pairing the six copies of a dart into three edges. -/
def cubeEdgeFun : CubeDart D → CubeDart D
  | (.n, x) => (.fe, x)
  | (.en, x) => (.nf, G.edge x)
  | (.f, x) => (.e, G.node (G.face x))
  | (.nf, x) => (.en, G.node (G.face x))
  | (.e, x) => (.f, G.edge x)
  | (.fe, x) => (.n, x)

/-- The edge permutation of the cube is an involution. -/
theorem cubeEdgeFun_involutive (u : CubeDart D) : G.cubeEdgeFun (G.cubeEdgeFun u) = u := by
  obtain ⟨t, x⟩ := u
  cases t <;> simp [cubeEdgeFun]

/-- The edge permutation of the cube. -/
def cubeEdge : Perm (CubeDart D) where
  toFun := G.cubeEdgeFun
  invFun := G.cubeEdgeFun
  left_inv := G.cubeEdgeFun_involutive
  right_inv := G.cubeEdgeFun_involutive

/-- The node permutation of the cube, as a function.  It has order three,
cycling the copies `n`, `en`, `fe` and the copies `f`, `nf`, `e`. -/
def cubeNodeFun : CubeDart D → CubeDart D
  | (.n, x) => (.en, G.node x)
  | (.en, x) => (.fe, x)
  | (.f, x) => (.nf, G.edge x)
  | (.nf, x) => (.e, G.node (G.face x))
  | (.e, x) => (.f, x)
  | (.fe, x) => (.n, G.face (G.edge x))

/-- The node permutation of the cube has order three. -/
theorem cubeNodeFun_cube (u : CubeDart D) :
    G.cubeNodeFun (G.cubeNodeFun (G.cubeNodeFun u)) = u := by
  obtain ⟨t, x⟩ := u
  cases t <;> simp [cubeNodeFun]

/-- The node permutation of the cube. -/
def cubeNode : Perm (CubeDart D) where
  toFun := G.cubeNodeFun
  invFun u := G.cubeNodeFun (G.cubeNodeFun u)
  left_inv := G.cubeNodeFun_cube
  right_inv := G.cubeNodeFun_cube

/-- The face permutation of the cube, as a function.  On the copies tagged `e`
it is the edge permutation of `G`, on those tagged `fe` it is the node
permutation, and it runs once around `n`, `en`, `f`, `nf` for each step of the
face permutation. -/
def cubeFaceFun : CubeDart D → CubeDart D
  | (.n, x) => (.en, x)
  | (.en, x) => (.f, x)
  | (.f, x) => (.nf, x)
  | (.nf, x) => (.n, G.face x)
  | (.e, x) => (.e, G.edge x)
  | (.fe, x) => (.fe, G.node x)

/-- The inverse of the face permutation of the cube, as a function. -/
def cubeFaceInvFun : CubeDart D → CubeDart D
  | (.n, x) => (.nf, G.face⁻¹ x)
  | (.en, x) => (.n, x)
  | (.f, x) => (.en, x)
  | (.nf, x) => (.f, x)
  | (.e, x) => (.e, G.edge⁻¹ x)
  | (.fe, x) => (.fe, G.node⁻¹ x)

/-- The face permutation of the cube. -/
def cubeFace : Perm (CubeDart D) where
  toFun := G.cubeFaceFun
  invFun := G.cubeFaceInvFun
  left_inv := by
    rintro ⟨t, x⟩
    cases t <;> simp [cubeFaceFun, cubeFaceInvFun]
  right_inv := by
    rintro ⟨t, x⟩
    cases t <;> simp [cubeFaceFun, cubeFaceInvFun]

/-- The three permutations of the cube compose to the identity. -/
theorem cube_cancel3 (u : CubeDart D) :
    G.cubeNodeFun (G.cubeFaceFun (G.cubeEdgeFun u)) = u := by
  obtain ⟨t, x⟩ := u
  cases t <;> simp [cubeEdgeFun, cubeFaceFun, cubeNodeFun]

/-- **The cube of a hypermap**: a plain cubic hypermap with six darts for each
dart of `G`, and one face for each edge, node and face of `G`. -/
def cube : Hypermap (CubeDart D) where
  edge := G.cubeEdge
  node := G.cubeNode
  face := G.cubeFace
  node_face_edge := by
    refine Equiv.ext fun u => ?_
    simp only [Perm.mul_apply, Perm.one_apply]
    exact G.cube_cancel3 u

@[simp] theorem cube_edge_apply (u : CubeDart D) : G.cube.edge u = G.cubeEdgeFun u := rfl
@[simp] theorem cube_node_apply (u : CubeDart D) : G.cube.node u = G.cubeNodeFun u := rfl
@[simp] theorem cube_face_apply (u : CubeDart D) : G.cube.face u = G.cubeFaceFun u := rfl

/-! ### The cube is plain and cubic -/

/-- The cube is plain: its edges are the three pairs of copies of a dart. -/
theorem plain_cube : G.cube.Plain where
  edge_edge u := G.cubeEdgeFun_involutive u
  edge_ne u := by
    obtain ⟨t, x⟩ := u
    cases t <;> simp [cubeEdgeFun]

/-- The cube is cubic: its nodes are the two triples of copies of a dart. -/
theorem cubic_cube : G.cube.Cubic :=
  ⟨fun u _ => G.cubeNodeFun_cube u, fun u _ => by
    obtain ⟨t, x⟩ := u
    cases t <;> simp [cubeNodeFun]⟩

/-- The cube has six times as many darts as its argument. -/
theorem card_cubeDart [Finite D] : Nat.card (CubeDart D) = 6 * Nat.card D := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, CubeTag.card_eq]

/-! ### The faces of the cube

A face of the cube is either an edge orbit of `G` (the copies tagged `e`), a
node orbit (the copies tagged `fe`), or a face orbit (the four remaining tags
together).  `cubeFaceClass` is the corresponding invariant of the face
permutation of the cube, and `cubeFaceQuotEquiv` promotes it to a bijection
between face orbits of the cube and the disjoint union of the edge, node and
face orbits of `G`. -/

/-- The orbit of the underlying dart, tagged by which of the three kinds of
face of `G.cube` a dart lies on. -/
def cubeFaceClass : CubeDart D →
    Quotient (SameCycle.setoid G.edge) ⊕ Quotient (SameCycle.setoid G.node) ⊕
      Quotient (SameCycle.setoid G.face)
  | (.e, x) => Sum.inl (Quotient.mk _ x)
  | (.fe, x) => Sum.inr (Sum.inl (Quotient.mk _ x))
  | (.n, x) => Sum.inr (Sum.inr (Quotient.mk _ x))
  | (.en, x) => Sum.inr (Sum.inr (Quotient.mk _ x))
  | (.f, x) => Sum.inr (Sum.inr (Quotient.mk _ x))
  | (.nf, x) => Sum.inr (Sum.inr (Quotient.mk _ x))

/-- The face class is invariant under the face permutation of the cube. -/
theorem cubeFaceClass_cubeFace (u : CubeDart D) :
    G.cubeFaceClass (G.cubeFaceFun u) = G.cubeFaceClass u := by
  have hq : ∀ (p : Perm D) (y : D),
      (Quotient.mk (SameCycle.setoid p) (p y)) = Quotient.mk (SameCycle.setoid p) y :=
    fun p y => Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl _ _))
  obtain ⟨t, x⟩ := u
  cases t <;> simp only [cubeFaceFun, cubeFaceClass, hq]

/-- The face class is constant on faces of the cube. -/
theorem cubeFaceClass_congr [Finite D] {u v : CubeDart D} (h : G.cube.CFace u v) :
    G.cubeFaceClass u = G.cubeFaceClass v := by
  replace h := (sameCycle_iff_reflTransGen G.cube.face u v).mp h
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih => rw [ih, hbc, cube_face_apply, G.cubeFaceClass_cubeFace]

/-- One step along a face of the cube. -/
theorem cface_cube_step (u : CubeDart D) : G.cube.CFace u (G.cubeFaceFun u) :=
  G.cube.cface_face u

/-- The copies tagged `e` carry the edge orbits of `G`. -/
theorem cface_cube_e [Finite D] {x y : D} (h : G.CEdge x y) :
    G.cube.CFace (CubeTag.e, x) (CubeTag.e, y) := by
  replace h := (sameCycle_iff_reflTransGen G.edge x y).mp h
  induction h with
  | refl => exact SameCycle.refl _ _
  | @tail b c _ hbc ih => rw [hbc]; exact ih.trans (G.cface_cube_step (CubeTag.e, b))

/-- The copies tagged `fe` carry the node orbits of `G`. -/
theorem cface_cube_fe [Finite D] {x y : D} (h : G.CNode x y) :
    G.cube.CFace (CubeTag.fe, x) (CubeTag.fe, y) := by
  replace h := (sameCycle_iff_reflTransGen G.node x y).mp h
  induction h with
  | refl => exact SameCycle.refl _ _
  | @tail b c _ hbc ih => rw [hbc]; exact ih.trans (G.cface_cube_step (CubeTag.fe, b))

/-- Four steps along a face of the cube advance the underlying dart by one
step of the face permutation of `G`. -/
theorem cface_cube_n_face (x : D) :
    G.cube.CFace (CubeTag.n, x) (CubeTag.n, G.face x) := by
  have h1 : G.cube.CFace (CubeTag.n, x) (CubeTag.en, x) := G.cface_cube_step _
  have h2 : G.cube.CFace (CubeTag.en, x) (CubeTag.f, x) := G.cface_cube_step _
  have h3 : G.cube.CFace (CubeTag.f, x) (CubeTag.nf, x) := G.cface_cube_step _
  have h4 : G.cube.CFace (CubeTag.nf, x) (CubeTag.n, G.face x) := G.cface_cube_step _
  exact ((h1.trans h2).trans h3).trans h4

/-- The four remaining copies together carry the face orbits of `G`. -/
theorem cface_cube_n [Finite D] {x y : D} (h : G.CFace x y) :
    G.cube.CFace (CubeTag.n, x) (CubeTag.n, y) := by
  replace h := (sameCycle_iff_reflTransGen G.face x y).mp h
  induction h with
  | refl => exact SameCycle.refl _ _
  | @tail b c _ hbc ih => rw [hbc]; exact ih.trans (G.cface_cube_n_face b)

/-- All four copies that carry face orbits lie on a common face of the cube. -/
theorem cface_cube_tag_n {t : CubeTag} (ht : t ≠ CubeTag.e) (ht' : t ≠ CubeTag.fe) (x : D) :
    G.cube.CFace (t, x) (CubeTag.n, x) := by
  have h1 : G.cube.CFace (CubeTag.n, x) (CubeTag.en, x) := G.cface_cube_step _
  have h2 : G.cube.CFace (CubeTag.en, x) (CubeTag.f, x) := G.cface_cube_step _
  have h3 : G.cube.CFace (CubeTag.f, x) (CubeTag.nf, x) := G.cface_cube_step _
  cases t
  · exact SameCycle.refl _ _
  · exact h1.symm
  · exact (h1.trans h2).symm
  · exact ((h1.trans h2).trans h3).symm
  · exact absurd rfl ht
  · exact absurd rfl ht'

/-- The faces of the cube are the edges, nodes and faces of `G`. -/
def cubeFaceQuotEquiv [Finite D] :
    Quotient (SameCycle.setoid G.cube.face) ≃
      Quotient (SameCycle.setoid G.edge) ⊕ Quotient (SameCycle.setoid G.node) ⊕
        Quotient (SameCycle.setoid G.face) where
  toFun := Quotient.lift G.cubeFaceClass fun _ _ h => G.cubeFaceClass_congr h
  invFun := Sum.elim
    (Quotient.lift (fun x => Quotient.mk _ (CubeTag.e, x)) fun _ _ h =>
      Quotient.sound (G.cface_cube_e h))
    (Sum.elim
      (Quotient.lift (fun x => Quotient.mk _ (CubeTag.fe, x)) fun _ _ h =>
        Quotient.sound (G.cface_cube_fe h))
      (Quotient.lift (fun x => Quotient.mk _ (CubeTag.n, x)) fun _ _ h =>
        Quotient.sound (G.cface_cube_n h)))
  left_inv q := by
    refine Quotient.inductionOn q fun u => ?_
    obtain ⟨t, x⟩ := u
    cases t
    · rfl
    · exact Quotient.sound (G.cface_cube_tag_n (by decide) (by decide) x).symm
    · exact Quotient.sound (G.cface_cube_tag_n (by decide) (by decide) x).symm
    · exact Quotient.sound (G.cface_cube_tag_n (by decide) (by decide) x).symm
    · rfl
    · rfl
  right_inv s := by
    rcases s with q | q | q <;> exact Quotient.inductionOn q fun x => rfl

/-- The cube has one face for each edge, node and face of `G`. -/
theorem cycleCount_cube_face [Finite D] :
    cycleCount G.cube.face = cycleCount G.edge + (cycleCount G.node + cycleCount G.face) := by
  rw [cycleCount, Nat.card_congr G.cubeFaceQuotEquiv, Nat.card_sum, Nat.card_sum]
  rfl

/-! ### The components of the cube -/

/-- A one-step E-link of the cube. -/
theorem glink_cube_edge (u : CubeDart D) :
    Relation.EqvGen G.cube.GLink u (G.cubeEdgeFun u) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

/-- A one-step N-link of the cube. -/
theorem glink_cube_node (u : CubeDart D) :
    Relation.EqvGen G.cube.GLink u (G.cubeNodeFun u) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl))

/-- A one-step F-link of the cube. -/
theorem glink_cube_face (u : CubeDart D) :
    Relation.EqvGen G.cube.GLink u (G.cubeFaceFun u) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl))

/-- All six copies of a dart lie in the same component of the cube. -/
theorem eqvGen_cube_tag (t : CubeTag) (x : D) :
    Relation.EqvGen G.cube.GLink (t, x) (CubeTag.nf, x) := by
  have h1 : Relation.EqvGen G.cube.GLink (CubeTag.n, x) (CubeTag.en, x) := G.glink_cube_face _
  have h2 : Relation.EqvGen G.cube.GLink (CubeTag.en, x) (CubeTag.f, x) := G.glink_cube_face _
  have h3 : Relation.EqvGen G.cube.GLink (CubeTag.f, x) (CubeTag.nf, x) := G.glink_cube_face _
  have he : Relation.EqvGen G.cube.GLink (CubeTag.e, x) (CubeTag.f, x) := G.glink_cube_node _
  have hfe : Relation.EqvGen G.cube.GLink (CubeTag.fe, x) (CubeTag.n, x) := G.glink_cube_edge _
  cases t
  · exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2 h3)
  · exact Relation.EqvGen.trans _ _ _ h2 h3
  · exact h3
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _ he h3
  · exact Relation.EqvGen.trans _ _ _ hfe
      (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2 h3))

/-- Links of `G` lift to paths of the cube. -/
theorem eqvGen_cube_of_glink {x y : D} (h : G.GLink x y) :
    Relation.EqvGen G.cube.GLink (CubeTag.nf, x) (CubeTag.nf, y) := by
  have h1 : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.n, z) (CubeTag.en, z) :=
    fun z => G.glink_cube_face _
  have h2 : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.en, z) (CubeTag.f, z) :=
    fun z => G.glink_cube_face _
  have h3 : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.f, z) (CubeTag.nf, z) :=
    fun z => G.glink_cube_face _
  have h4 : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.nf, z) (CubeTag.n, G.face z) :=
    fun z => G.glink_cube_face _
  have hen : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.en, z) (CubeTag.nf, G.edge z) :=
    fun z => G.glink_cube_edge _
  have hn : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.n, z) (CubeTag.en, G.node z) :=
    fun z => G.glink_cube_node _
  have hnf : ∀ z : D, Relation.EqvGen G.cube.GLink (CubeTag.nf, z) (CubeTag.n, z) :=
    fun z => Relation.EqvGen.symm _ _
      (Relation.EqvGen.trans _ _ _ (h1 z) (Relation.EqvGen.trans _ _ _ (h2 z) (h3 z)))
  rcases h with rfl | rfl | rfl
  · exact Relation.EqvGen.trans _ _ _ (hnf x)
      (Relation.EqvGen.trans _ _ _ (h1 x) (hen x))
  · exact Relation.EqvGen.trans _ _ _ (hnf x)
      (Relation.EqvGen.trans _ _ _ (hn x)
        (Relation.EqvGen.trans _ _ _ (h2 (G.node x)) (h3 (G.node x))))
  · exact Relation.EqvGen.trans _ _ _ (h4 x)
      (Relation.EqvGen.trans _ _ _ (h1 (G.face x))
        (Relation.EqvGen.trans _ _ _ (h2 (G.face x)) (h3 (G.face x))))

/-- Paths of `G` lift to paths of the cube. -/
theorem eqvGen_cube_of_eqvGen {x y : D} (h : Relation.EqvGen G.GLink x y) :
    Relation.EqvGen G.cube.GLink (CubeTag.nf, x) (CubeTag.nf, y) := by
  induction h with
  | rel a b hab => exact G.eqvGen_cube_of_glink hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Each of the three permutations of the cube moves a dart within the
component of the underlying dart. -/
theorem eqvGen_base_cube_edge (u : CubeDart D) :
    Relation.EqvGen G.GLink u.2 (G.cubeEdgeFun u).2 := by
  have gE : ∀ z : D, Relation.EqvGen G.GLink z (G.edge z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_edge z)
  have gN : ∀ z : D, Relation.EqvGen G.GLink z (G.node z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_node z)
  have gF : ∀ z : D, Relation.EqvGen G.GLink z (G.face z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_face z)
  obtain ⟨t, x⟩ := u
  cases t
  · exact Relation.EqvGen.refl _
  · exact gE x
  · exact Relation.EqvGen.trans _ _ _ (gF x) (gN (G.face x))
  · exact Relation.EqvGen.trans _ _ _ (gF x) (gN (G.face x))
  · exact gE x
  · exact Relation.EqvGen.refl _

theorem eqvGen_base_cube_node (u : CubeDart D) :
    Relation.EqvGen G.GLink u.2 (G.cubeNodeFun u).2 := by
  have gE : ∀ z : D, Relation.EqvGen G.GLink z (G.edge z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_edge z)
  have gN : ∀ z : D, Relation.EqvGen G.GLink z (G.node z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_node z)
  have gF : ∀ z : D, Relation.EqvGen G.GLink z (G.face z) :=
    fun z => Relation.EqvGen.rel _ _ (G.glink_face z)
  obtain ⟨t, x⟩ := u
  cases t
  · exact gN x
  · exact Relation.EqvGen.refl _
  · exact gE x
  · exact Relation.EqvGen.trans _ _ _ (gF x) (gN (G.face x))
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _ (gE x) (gF (G.edge x))

theorem eqvGen_base_cube_face (u : CubeDart D) :
    Relation.EqvGen G.GLink u.2 (G.cubeFaceFun u).2 := by
  obtain ⟨t, x⟩ := u
  cases t
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (G.glink_face x)
  · exact Relation.EqvGen.rel _ _ (G.glink_edge x)
  · exact Relation.EqvGen.rel _ _ (G.glink_node x)

/-- A link of the cube projects to a path of `G`. -/
theorem eqvGen_base_of_glink_cube {u v : CubeDart D} (h : G.cube.GLink u v) :
    Relation.EqvGen G.GLink u.2 v.2 := by
  rcases h with rfl | rfl | rfl
  exacts [G.eqvGen_base_cube_edge u, G.eqvGen_base_cube_node u, G.eqvGen_base_cube_face u]

/-- A path of the cube projects to a path of `G`. -/
theorem eqvGen_base_of_eqvGen_cube {u v : CubeDart D}
    (h : Relation.EqvGen G.cube.GLink u v) : Relation.EqvGen G.GLink u.2 v.2 := by
  induction h with
  | rel a b hab => exact G.eqvGen_base_of_glink_cube hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The components of the cube are the components of `G`. -/
def cubeCompEquiv : Quotient G.cube.gcompSetoid ≃ Quotient G.gcompSetoid where
  toFun := Quotient.lift (fun u => Quotient.mk _ u.2) fun _ _ h =>
    Quotient.sound (G.eqvGen_base_of_eqvGen_cube h)
  invFun := Quotient.lift (fun x => Quotient.mk _ (CubeTag.nf, x)) fun _ _ h =>
    Quotient.sound (G.eqvGen_cube_of_eqvGen h)
  left_inv q := by
    refine Quotient.inductionOn q fun u => ?_
    obtain ⟨t, x⟩ := u
    exact Quotient.sound (Relation.EqvGen.symm _ _ (G.eqvGen_cube_tag t x))
  right_inv q := Quotient.inductionOn q fun _ => rfl

/-- The cube has the same number of components as `G`. -/
theorem compCount_cube : G.cube.compCount = G.compCount :=
  Nat.card_congr G.cubeCompEquiv

/-- The cube is connected exactly when `G` is. -/
theorem connected_cube : G.cube.Connected ↔ G.Connected := by
  simp only [Connected, compCount_cube]

/-! ### Genus and planarity -/

/-- The cube has the same genus as `G`: it has six times as many darts, three
times as many edges, twice as many nodes, and as many faces as `G` has edges,
nodes and faces together. -/
theorem genus_cube [Finite D] : G.cube.genus = G.genus := by
  have hcard : Nat.card (CubeDart D) = 6 * Nat.card D := card_cubeDart
  have hE := G.plain_cube.card_eq
  have hN := G.cubic_cube.card_eq
  rw [hcard] at hE hN
  simp only [genus, EulerLhs, EulerRhs, G.compCount_cube, G.cycleCount_cube_face, hcard]
  omega

/-- The cube is planar exactly when `G` is. -/
theorem planar_cube [Finite D] : G.cube.Planar ↔ G.Planar := by
  simp only [Planar, genus_cube]

/-! ### Bridges -/

/-- The cube is bridgeless exactly when `G` is. -/
theorem bridgeless_cube [Finite D] : G.cube.Bridgeless ↔ G.Bridgeless := by
  constructor
  · intro h x hx
    refine h (CubeTag.en, x) ?_
    have h1 : G.cube.CFace (CubeTag.en, x) (CubeTag.n, x) :=
      G.cface_cube_tag_n (by decide) (by decide) x
    have h2 : G.cube.CFace (CubeTag.n, x) (CubeTag.n, G.edge x) := G.cface_cube_n hx
    have h3 : G.cube.CFace (CubeTag.nf, G.edge x) (CubeTag.n, G.edge x) :=
      G.cface_cube_tag_n (by decide) (by decide) (G.edge x)
    exact (h1.trans h2).trans h3.symm
  · intro h u hu
    have hcl := G.cubeFaceClass_congr hu
    obtain ⟨t, x⟩ := u
    cases t <;>
      simp only [cube_edge_apply, cubeEdgeFun, cubeFaceClass, Sum.inr.injEq,
        reduceCtorEq] at hcl
    · exact h x (Quotient.exact hcl)
    · have hx : G.CFace x (G.node (G.face x)) := Quotient.exact hcl
      refine h (G.node (G.face x)) ?_
      rw [G.faceK]
      exact hx.symm

/-! ### Colouring -/

/-- A four-colouring of the cube restricts to a four-colouring of `G`: this is
the reduction of the Four Colour Theorem to plain cubic maps. -/
theorem FourColorable.of_cube (h : G.cube.FourColorable) : G.FourColorable := by
  obtain ⟨k, hk⟩ := h
  have hnf : ∀ x : D, k (CubeTag.n, G.face x) = k (CubeTag.nf, x) :=
    fun x => hk.face (CubeTag.nf, x)
  have hn : ∀ x : D, k (CubeTag.en, x) = k (CubeTag.n, x) :=
    fun x => hk.face (CubeTag.n, x)
  have hen : ∀ x : D, k (CubeTag.f, x) = k (CubeTag.en, x) :=
    fun x => hk.face (CubeTag.en, x)
  have hf : ∀ x : D, k (CubeTag.nf, x) = k (CubeTag.f, x) :=
    fun x => hk.face (CubeTag.f, x)
  have hface : ∀ x : D, k (CubeTag.nf, G.face x) = k (CubeTag.nf, x) := by
    intro x
    rw [hf (G.face x), hen (G.face x), hn (G.face x), hnf x]
  refine ⟨fun x => k (CubeTag.nf, x), ⟨fun x => ?_, hface⟩⟩
  have he : k (CubeTag.nf, G.edge x) ≠ k (CubeTag.en, x) := hk.edge (CubeTag.en, x)
  have hx : k (CubeTag.nf, x) = k (CubeTag.en, x) := (hf x).trans (hen x)
  rw [← hx] at he
  exact he

end Hypermap

end FourColor

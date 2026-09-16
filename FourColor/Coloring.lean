import FourColor.Chromogram
import FourColor.Geometry
import FourColor.Path

/-!
# Colourings of a hypermap

A *colouring* of a hypermap assigns a colour to each dart, constant on each
face and different at the two ends of every E-link — so adjacent faces get
different colours.  Four-colourability of a hypermap is the existence of such a
colouring, and the Four Colour Theorem for hypermaps is that every planar
hypermap has one.

The dual notion, constant on *nodes* rather than faces, is graph colouring:
colouring the hypermap `dual G` is the same as graph-colouring `G`.

## Main definitions

* `Hypermap.Coloring`, `Hypermap.FourColorable` — map colourings.
* `Hypermap.GraphColoring`, `Hypermap.GraphFourColorable` — graph colourings.
* `Hypermap.RingTrace` — the edge trace of a colouring along a ring of darts.
* `Hypermap.CcColoring`, `Hypermap.CcColorable`, `Hypermap.CcRingTrace` —
  contract colourings, for the contract given by a list of darts.
* `Hypermap.MinimalCounterExample` — a minimal counter-example to the Four
  Colour Theorem for hypermaps.
* `Hypermap.GoodRingArity`, `Hypermap.AtRadius2`, `Hypermap.Radius2`,
  `Hypermap.Embeddable` — the geometrical requirements on a configuration map.
* `Hypermap.Sparse`, `Hypermap.Triad`, `Hypermap.ValidContract`,
  `Hypermap.CReducible` — the semantic requirements on a configuration map.
* `Hypermap.EdgeCentral`, `Hypermap.Preembedding` — partial hypermap morphisms.


## Main results

* `Hypermap.coloring_dual_iff`, `Hypermap.fourColorable_dual_iff` — duality.
* `Hypermap.Coloring.of_mirror`, `Hypermap.FourColorable.of_mirror` — mirroring.
* `Hypermap.decidableFourColorable` — four-colourability is decidable.
* `Hypermap.FourColorable.bridgeless` — a colourable map is bridgeless.
* `Hypermap.MinimalCounterExample.mirror` — mirroring a minimal
  counter-example.
* `Hypermap.MinimalCounterExample.cubic` — a minimal counter-example is cubic.
-/

namespace FourColor

open Equiv Equiv.Perm in
/-- A function that does not change along the steps of a permutation is
constant on each of its cycles. -/
theorem congr_of_sameCycle {D : Type*} {α : Sort*} {f : Perm D} {F : D → α}
    (hF : ∀ z, F (f z) = F z) {x y : D} (h : f.SameCycle x y) : F x = F y := by
  obtain ⟨i, rfl⟩ := h
  have hinv : ∀ z : D, F (f⁻¹ z) = F z := by
    intro z
    simpa using (hF (f⁻¹ z)).symm
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one, Perm.mul_apply, hF]
      exact ih
  | pred n ih =>
      rw [show (-(n : ℤ) - 1) = -1 + -(n : ℤ) by ring, zpow_add, zpow_neg_one, Perm.mul_apply,
        hinv]
      exact ih

namespace Hypermap

open Equiv Equiv.Perm

variable {D : Type*} (G : Hypermap D)

/-- A map colouring: one colour per face, different across every E-link. -/
structure Coloring (k : D → Color) : Prop where
  /-- The two ends of an E-link have different colours. -/
  edge : ∀ x, k (G.edge x) ≠ k x
  /-- The colour is constant on each face. -/
  face : ∀ x, k (G.face x) = k x

/-- A hypermap is four-colourable when it has a map colouring. -/
def FourColorable : Prop := ∃ k : D → Color, G.Coloring k

/-- A graph colouring: one colour per node, different across every E-link. -/
structure GraphColoring (k : D → Color) : Prop where
  /-- The two ends of an E-link have different colours. -/
  edge : ∀ x, k (G.edge x) ≠ k x
  /-- The colour is constant on each node. -/
  node : ∀ x, k (G.node x) = k x

/-- A hypermap is graph-four-colourable when it has a graph colouring. -/
def GraphFourColorable : Prop := ∃ k : D → Color, G.GraphColoring k

/-- The edge colouring trace of a colouring along a ring of darts. -/
def RingTrace (r : List D) (et : List Color) : Prop :=
  ∃ k, G.Coloring k ∧ et = trace (r.map k)

variable {G}

/-- Recolouring by an injection is again a colouring. -/
theorem Coloring.comp {k : D → Color} {h : Color → Color} (hinj : Function.Injective h)
    (hk : G.Coloring k) : G.Coloring (h ∘ k) where
  edge x := fun hc => hk.edge x (hinj hc)
  face x := congrArg h (hk.face x)

/-! ### Duality and mirroring -/

/-- Colouring the dual is graph-colouring the original. -/
theorem coloring_dual_iff (k : D → Color) : G.dual.Coloring k ↔ G.GraphColoring k := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have hinv : G.edge⁻¹ (G.edge x) = x := by simp
      have hx := h.edge (G.edge x)
      rw [dual_edge, hinv] at hx
      exact fun hc => hx hc.symm
    · have hinv : G.node⁻¹ (G.node x) = x := by simp
      have hx := h.face (G.node x)
      rw [dual_face, hinv] at hx
      exact hx.symm
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have hinv : G.edge (G.edge⁻¹ x) = x := by simp
      have hx := h.edge (G.edge⁻¹ x)
      rw [hinv] at hx
      rw [dual_edge]
      exact fun hc => hx hc.symm
    · have hinv : G.node (G.node⁻¹ x) = x := by simp
      have hx := h.node (G.node⁻¹ x)
      rw [hinv] at hx
      rw [dual_face]
      exact hx.symm

theorem fourColorable_dual_iff : G.dual.FourColorable ↔ G.GraphFourColorable :=
  exists_congr fun k => coloring_dual_iff k

/-- A colouring of the mirror is a colouring. -/
theorem Coloring.of_mirror {k : D → Color} (h : G.mirror.Coloring k) : G.Coloring k := by
  have hface : ∀ x, k (G.face x) = k x := by
    intro x
    have hinv : G.face⁻¹ (G.face x) = x := by simp
    have hx := h.face (G.face x)
    rw [mirror_face, hinv] at hx
    exact hx.symm
  refine ⟨fun x => ?_, hface⟩
  have hx : G.node (G.face (G.edge x)) = x := G.edgeK x
  have he := h.edge (G.face (G.edge x))
  rw [mirror_edge, Perm.mul_apply, hx, hface x, hface (G.edge x)] at he
  exact fun hc => he hc.symm

theorem FourColorable.of_mirror (h : G.mirror.FourColorable) : G.FourColorable := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.of_mirror⟩

/-! ### Decidability -/

instance decidableColoring [Fintype D] [DecidableEq D] (k : D → Color) :
    Decidable (G.Coloring k) :=
  decidable_of_iff ((∀ x, k (G.edge x) ≠ k x) ∧ ∀ x, k (G.face x) = k x)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.edge, h.face⟩⟩

instance decidableGraphColoring [Fintype D] [DecidableEq D] (k : D → Color) :
    Decidable (G.GraphColoring k) :=
  decidable_of_iff ((∀ x, k (G.edge x) ≠ k x) ∧ ∀ x, k (G.node x) = k x)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.edge, h.node⟩⟩

instance decidableFourColorable [Fintype D] [DecidableEq D] : Decidable G.FourColorable :=
  inferInstanceAs (Decidable (∃ k : D → Color, G.Coloring k))

instance decidableGraphFourColorable [Fintype D] [DecidableEq D] :
    Decidable G.GraphFourColorable :=
  inferInstanceAs (Decidable (∃ k : D → Color, G.GraphColoring k))

/-- Ring traces are decidable, which the Birkhoff bound needs.  The reference
has to enumerate colourings dart by dart; here the colourings form a finite
type, so the quantifier is decidable outright. -/
instance decidableRingTrace [Fintype D] [DecidableEq D] (r : List D) (et : List Color) :
    Decidable (G.RingTrace r et) :=
  inferInstanceAs (Decidable (∃ k : D → Color, G.Coloring k ∧ et = trace (r.map k)))

/-! ### Colourings and faces -/

/-- A colouring is constant on faces. -/
theorem Coloring.cface {k : D → Color} (hk : G.Coloring k) {x y : D} (h : G.CFace x y) :
    k x = k y :=
  congr_of_sameCycle hk.face h

/-- A colourable map is bridgeless: the two ends of an E-link get different
colours, so they cannot share a face. -/
theorem FourColorable.bridgeless (h : G.FourColorable) : G.Bridgeless := by
  obtain ⟨k, hk⟩ := h
  exact fun x hx => hk.edge x (hk.cface hx).symm

/-! ### Contract colourings

A *contract* is a list `cc` of darts of a plain map; the E-links to be
contracted are those of the darts of its edge closure `Hypermap.insertE cc`.
A contract colouring is constant on faces and gives the two ends of an E-link
the same colour exactly when that link is contracted. -/

variable (G)

/-- A contract colouring for the contract `cc`. -/
structure CcColoring (cc : List D) (k : D → Color) : Prop where
  /-- The ends of an E-link share a colour exactly when the link is
  contracted. -/
  edge : ∀ x, k (G.edge x) = k x ↔ x ∈ G.insertE cc
  /-- The colour is constant on each face. -/
  face : ∀ x, k (G.face x) = k x

/-- There is a contract colouring for `cc`. -/
def CcColorable (cc : List D) : Prop := ∃ k : D → Color, G.CcColoring cc k

/-- The edge colouring trace of a contract colouring along a ring of darts. -/
def CcRingTrace (cc r : List D) (et : List Color) : Prop :=
  ∃ k, G.CcColoring cc k ∧ et = trace (r.map k)

variable {G}

/-- A contract colouring is constant on faces. -/
theorem CcColoring.cface {cc : List D} {k : D → Color} (hk : G.CcColoring cc k) {x y : D}
    (h : G.CFace x y) : k x = k y :=
  congr_of_sameCycle hk.face h

/-- A contract colouring for the empty contract is a colouring. -/
theorem ccColoring_nil_iff {k : D → Color} : G.CcColoring [] k ↔ G.Coloring k := by
  constructor
  · exact fun h => ⟨fun x hx => by simpa using (h.edge x).mp hx, h.face⟩
  · exact fun h => ⟨fun x => by simp [fun hc => h.edge x hc], h.face⟩

/-- A contract ring trace for the empty contract is a ring trace. -/
theorem ccRingTrace_nil_iff {r : List D} {et : List Color} :
    G.CcRingTrace [] r et ↔ G.RingTrace r et :=
  exists_congr fun _ => and_congr_left fun _ => ccColoring_nil_iff

/-! ### Minimal counter-examples -/

section MinimalCounterExample

universe v

/-- A minimal counter-example to the Four Colour Theorem for hypermaps: a
planar, bridgeless, plain and precubic hypermap that is not four-colourable,
all of whose smaller instances are.  Such a map is in fact cubic, connected and
pentagonal; the first of these is proved below. -/
structure MinimalCounterExample {E : Type v} [Finite E] (H : Hypermap E) : Prop where
  /-- The map is planar, bridgeless, plain and precubic. -/
  base : H.PlanarBridgelessPlainPrecubic
  /-- The map is a counter-example. -/
  noncolorable : ¬ H.FourColorable
  /-- Every smaller planar bridgeless plain precubic map is four-colourable. -/
  minimal : ∀ {E' : Type v} [Finite E'] (H' : Hypermap E'),
    H'.PlanarBridgelessPlainPrecubic → Nat.card E' < Nat.card E → H'.FourColorable

variable [Finite D]

/-- A minimal counter-example is planar. -/
theorem MinimalCounterExample.planar (h : G.MinimalCounterExample) : G.Planar :=
  h.base.base.base.planar

/-- A minimal counter-example is bridgeless. -/
theorem MinimalCounterExample.bridgeless (h : G.MinimalCounterExample) : G.Bridgeless :=
  h.base.base.base.bridgeless

/-- A minimal counter-example is plain. -/
theorem MinimalCounterExample.plain (h : G.MinimalCounterExample) : G.Plain :=
  h.base.base.plain

/-- A minimal counter-example is precubic. -/
theorem MinimalCounterExample.precubic (h : G.MinimalCounterExample) : G.Precubic :=
  h.base.precubic

/-- Mirroring a minimal counter-example gives a minimal counter-example; this is
used for symmetry arguments and for flipped configuration matches. -/
theorem MinimalCounterExample.mirror (h : G.MinimalCounterExample) :
    G.mirror.MinimalCounterExample where
  base :=
    ⟨⟨⟨(planar_mirror G).mpr h.planar, (bridgeless_mirror G).mpr h.bridgeless⟩,
      (plain_mirror G).mpr h.plain⟩, (precubic_mirror G).mpr h.precubic⟩
  noncolorable hc := h.noncolorable hc.of_mirror
  minimal H' hH' hcard := h.minimal H' hH' hcard

end MinimalCounterExample

/-! ### A minimal counter-example is cubic

A node of fewer than three darts can be removed by two Walkup transforms; the
result is again planar, bridgeless, plain and precubic, so it is four-colourable
by minimality, and its colouring extends back to the original map. -/

section WalkupCubic

variable [DecidableEq D] {x n : D}

/-- The edge permutation of the map obtained by deleting `x` and `n = node x`,
read on the darts of the original map.  Deleting `x` merges the E-links at `x`
and at `n` into a three-dart E-cycle, and deleting `n` cuts that back down to
the E-link between `edge x` and `edge n`. -/
private def walkupEdge2 (G : Hypermap D) (x n y : D) : D :=
  if y = G.edge n then G.edge x else if y = G.edge x then G.edge n else G.edge y

private theorem walkupEdge2_edge_n (G : Hypermap D) (x n : D) :
    walkupEdge2 G x n (G.edge n) = G.edge x := by simp [walkupEdge2]

private theorem walkupEdge2_edge_x (G : Hypermap D) {x n : D} (hxn : n ≠ x) :
    walkupEdge2 G x n (G.edge x) = G.edge n := by
  have hne : G.edge x ≠ G.edge n := fun hc => hxn (G.edge.injective hc).symm
  simp [walkupEdge2, hne]

private theorem walkupEdge2_other (G : Hypermap D) {x n z : D} (h1 : z ≠ G.edge n)
    (h2 : z ≠ G.edge x) : walkupEdge2 G x n z = G.edge z := by simp [walkupEdge2, h1, h2]

private theorem walkupEdge2_walkupEdge2 (hp : G.Plain) (hxn : n ≠ x) {y : D} (hy1 : y ≠ x)
    (hy2 : y ≠ n) : walkupEdge2 G x n (walkupEdge2 G x n y) = y := by
  by_cases h1 : y = G.edge n
  · rw [h1, walkupEdge2_edge_n, walkupEdge2_edge_x G hxn]
  · by_cases h2 : y = G.edge x
    · rw [h2, walkupEdge2_edge_x G hxn, walkupEdge2_edge_n]
    · rw [walkupEdge2_other G h1 h2,
        walkupEdge2_other G (fun hc => hy2 (G.edge.injective hc))
          (fun hc => hy1 (G.edge.injective hc)),
        hp.edge_edge]

private theorem walkupEdge2_ne (hp : G.Plain) (hxn : n ≠ x) {y : D} :
    walkupEdge2 G x n y ≠ y := by
  have hne : G.edge x ≠ G.edge n := fun hc => hxn (G.edge.injective hc).symm
  by_cases h1 : y = G.edge n
  · rw [h1, walkupEdge2_edge_n]; exact hne
  · by_cases h2 : y = G.edge x
    · rw [h2, walkupEdge2_edge_x G hxn]; exact fun hc => hne hc.symm
    · rw [walkupEdge2_other G h1 h2]; exact hp.edge_ne y

/-- The explicit edge permutation of `walkupE` for a plain map with
`node x = n`. -/
private theorem walkupE_edge_val' (hp : G.Plain) (hn : G.node x = n) (v : Walkup G x) :
    ((G.walkupE x).edge v).val =
      if v.val = n then G.edge x else if v.val = G.edge x then G.edge n else G.edge v.val := by
  have hface : (G.face (G.edge v.val) = x) ↔ (v.val = n) := by
    constructor
    · intro hv
      have h1 := G.edgeK v.val
      rw [hv] at h1
      rw [← h1]
      exact hn
    · intro hv
      rw [hv, ← hn]
      exact G.nodeK x
  have hedge : (G.edge v.val = x) ↔ (v.val = G.edge x) := by
    constructor
    · intro hv
      have h1 := congrArg (G.edge : D → D) hv
      rwa [hp.edge_edge] at h1
    · intro hv
      rw [hv, hp.edge_edge]
  rw [walkupE_edge_val]
  simp only [skipEdgeFun, ite_eq_right (hp.edge_ne x), hface, hedge, hn]

/-- Deleting `x` makes `n = node x` a fixed dart of `node`. -/
private theorem walkupE_node_self (hn : G.node x = n) (hnn : G.node n = x) (hxn : n ≠ x) :
    (G.walkupE x).node (⟨n, hxn⟩ : Walkup G x) = ⟨n, hxn⟩ := by
  apply Subtype.ext
  have h1 : G.node (⟨n, hxn⟩ : Walkup G x).val = x := hnn
  rw [walkupE_node, skip_val_of_eq h1]
  exact hn

/-- Deleting `x` and then `n` leaves `node` unchanged. -/
private theorem walkup2_node_val (hn : G.node x = n) (hnn : G.node n = x) (hxn : n ≠ x)
    (w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)) :
    (((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).node w).val.val = G.node w.val.val := by
  have hy1 : w.val.val ≠ x := w.val.property
  have hy2 : w.val.val ≠ n := fun hh => w.property (Subtype.ext hh)
  have h1 : G.node w.val.val ≠ x := fun hc => hy2 (G.node.injective (hc.trans hnn.symm))
  have h2 : ((G.walkupE x).node w.val).val = G.node w.val.val := by
    rw [walkupE_node]; exact skip_val_of_ne h1
  have h3 : (G.walkupE x).node w.val ≠ (⟨n, hxn⟩ : Walkup G x) := by
    intro hc
    have h4 := congrArg Subtype.val hc
    rw [h2] at h4
    exact hy1 (G.node.injective (h4.trans hn.symm))
  rw [walkupE_node, skip_val_of_ne h3, h2]

/-- Deleting `x` and then `n` turns `edge` into `walkupEdge2`. -/
private theorem walkup2_edge_val (hp : G.Plain) (hn : G.node x = n) (hnn : G.node n = x)
    (hxn : n ≠ x) (w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)) :
    (((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).edge w).val.val =
      walkupEdge2 G x n w.val.val := by
  have hval : ∀ v : Walkup G x, v = (⟨n, hxn⟩ : Walkup G x) ↔ v.val = n :=
    fun v => ⟨fun hv => congrArg Subtype.val hv, fun hv => Subtype.ext hv⟩
  have hy1 : w.val.val ≠ x := w.val.property
  have hy2 : w.val.val ≠ n := fun hh => w.property (Subtype.ext hh)
  have hnu : (G.walkupE x).node (⟨n, hxn⟩ : Walkup G x) = ⟨n, hxn⟩ :=
    walkupE_node_self hn hnn hxn
  have hEu : ((G.walkupE x).edge (⟨n, hxn⟩ : Walkup G x)).val = G.edge x := by
    rw [walkupE_edge_val' hp hn]; simp
  have hEw : ((G.walkupE x).edge w.val).val =
      if w.val.val = G.edge x then G.edge n else G.edge w.val.val := by
    simp only [walkupE_edge_val' hp hn, ite_eq_right hy2]
  have hc2 : ¬ ((G.walkupE x).face ((G.walkupE x).edge w.val) = (⟨n, hxn⟩ : Walkup G x)) := by
    intro hc
    have h1 := (G.walkupE x).edgeK w.val
    rw [hc, hnu] at h1
    exact w.property h1.symm
  have hc3 : ((G.walkupE x).edge w.val = (⟨n, hxn⟩ : Walkup G x)) ↔ w.val.val = G.edge n := by
    rw [hval, hEw]
    by_cases hb : w.val.val = G.edge x
    · rw [ite_eq_left hb]
      constructor
      · intro hc
        exact absurd hc (hp.edge_ne n)
      · intro hc
        exact absurd (hb.symm.trans hc) fun hh => hxn (G.edge.injective hh).symm
    · rw [ite_eq_right hb]
      constructor
      · intro hc
        have h6 := congrArg (G.edge : D → D) hc
        rwa [hp.edge_edge] at h6
      · intro hc
        rw [hc, hp.edge_edge]
  rw [walkupE_edge_val]
  simp only [skipEdgeFun]
  by_cases hc1 : (G.walkupE x).edge (⟨n, hxn⟩ : Walkup G x) = ⟨n, hxn⟩
  · have hcross : G.edge x = n := by
      have h5 := congrArg Subtype.val hc1
      rw [hEu] at h5
      exact h5
    have hen' : G.edge n = x := by
      have h6 := congrArg (G.edge : D → D) hcross
      rw [hp.edge_edge] at h6
      exact h6.symm
    have hd1 : ¬ (w.val.val = G.edge n) := by rw [hen']; exact hy1
    simp only [ite_eq_left hc1, hEw, walkupEdge2, ite_eq_right hd1]
  · simp only [ite_eq_right hc1, ite_eq_right hc2]
    by_cases hc3' : (G.walkupE x).edge w.val = (⟨n, hxn⟩ : Walkup G x)
    · simp only [ite_eq_left hc3', hnu, hEu, walkupEdge2, ite_eq_left (hc3.mp hc3')]
    · have hd2 : ¬ (w.val.val = G.edge n) := fun hh => hc3' (hc3.mpr hh)
      simp only [ite_eq_right hc3', hEw, walkupEdge2, ite_eq_right hd2]

/-- Deleting `x` and then `n` does not change which darts share a face. -/
private theorem walkup2_cface [Finite D] (hxn : n ≠ x)
    (w w' : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)) :
    ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).CFace w w' ↔
      G.CFace w.val.val w'.val.val :=
  (sameCycle_skip ((G.walkupE x).face) (⟨n, hxn⟩ : Walkup G x) w w').trans
    (sameCycle_skip G.face x w.val w'.val)

end WalkupCubic

section MinimalCubic

variable [Finite D]

/-- **A minimal counter-example is cubic.**  If a node of `G` had fewer than
three darts it would have exactly two, `x` and `n = node x`.  Deleting both by
two Walkup transforms gives a smaller planar bridgeless plain precubic map,
which is four-colourable by minimality; its colouring assigns a colour to every
face of `G` except possibly the faces of `x` and of `n`, and those two can be
coloured apart, contradicting non-colourability. -/
theorem MinimalCounterExample.cubic (h : G.MinimalCounterExample) : G.Cubic := by
  classical
  have hp := h.plain
  have hb := h.bridgeless
  have hcf : ∀ a b : D, G.face a = b → G.CFace a b := fun a b hab => ⟨1, by simpa using hab⟩
  have key : ∀ x : D, Function.minimalPeriod G.node x = 3 := by
    intro x
    by_contra hne3
    have hpos : 0 < Function.minimalPeriod (G.node : D → D) x :=
      Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts G.node x)
    have hle : Function.minimalPeriod (G.node : D → D) x ≤ 3 := h.precubic x
    have hxn : G.node x ≠ x := by
      intro hc
      have hfe : G.face (G.edge x) = x := by
        have h1 := G.nodeK x
        rwa [hc] at h1
      exact hb x (hcf _ _ hfe).symm
    have hne1 : Function.minimalPeriod (G.node : D → D) x ≠ 1 := fun hc =>
      hxn (Function.minimalPeriod_eq_one_iff_isFixedPt.mp hc)
    have hm2 : Function.minimalPeriod (G.node : D → D) x = 2 := by omega
    have hnn : G.node (G.node x) = x := by
      have h1 := Function.iterate_minimalPeriod (f := (G.node : D → D)) (x := x)
      rw [hm2] at h1
      exact h1
    obtain ⟨n, hn⟩ : ∃ n, G.node x = n := ⟨_, rfl⟩
    rw [hn] at hxn hnn
    have : Fintype D := Fintype.ofFinite D
    have : Fintype (Walkup G x) := Fintype.ofFinite _
    have hfex : G.face (G.edge x) = n := by
      have h1 := G.nodeK n
      rwa [hnn] at h1
    have hfen : G.face (G.edge n) = x := by
      have h1 := G.nodeK x
      rwa [hn] at h1
    have hE := walkup2_edge_val hp hn hnn hxn
    have hN := walkup2_node_val hn hnn hxn
    have hF := walkup2_cface (G := G) hxn
    -- the doubly reduced map is plain
    have hplainH : ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).Plain := by
      constructor
      · intro w
        apply Subtype.ext
        apply Subtype.ext
        rw [hE, hE]
        exact walkupEdge2_walkupEdge2 hp hxn w.val.property
          (fun hh => w.property (Subtype.ext hh))
      · intro w hc
        have h1 : ((((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).edge w)).val.val
            = w.val.val := congrArg Subtype.val (congrArg Subtype.val hc)
        rw [hE] at h1
        exact walkupEdge2_ne hp hxn h1
    -- it is bridgeless
    have hbH : ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).Bridgeless := by
      intro w hc
      rw [hF] at hc
      rw [hE] at hc
      by_cases h1 : w.val.val = G.edge n
      · rw [h1, walkupEdge2_edge_n] at hc
        exact hb x ((hcf _ _ hfen).symm.trans hc)
      · by_cases h2 : w.val.val = G.edge x
        · rw [h2, walkupEdge2_edge_x G hxn] at hc
          exact hb x (hc.trans (hcf _ _ hfen)).symm
        · rw [walkupEdge2_other G h1 h2] at hc
          exact hb _ hc
    -- it is precubic
    have hpcH : ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).Precubic := by
      have hiter : ∀ (m : ℕ) (w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)),
          ((((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).node : _ → _)^[m] w).val.val
            = (G.node : D → D)^[m] w.val.val := by
        intro m
        induction m with
        | zero => intro w; rfl
        | succ m ih =>
          intro w
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hN]
      intro w
      have hmp := h.precubic w.val.val
      have hpp : 0 < Function.minimalPeriod (G.node : D → D) w.val.val :=
        Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts G.node _)
      have hper : ((((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).node : _ → _)^[
          Function.minimalPeriod (G.node : D → D) w.val.val] w) = w := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hiter]
        exact Function.iterate_minimalPeriod
      exact le_trans (Function.IsPeriodicPt.minimalPeriod_le hpp hper) hmp
    -- it is planar and smaller
    have hpl2 : ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).Planar :=
      planar_walkupE (G.walkupE x) (⟨n, hxn⟩ : Walkup G x) (planar_walkupE G x h.planar)
    have hlt : Nat.card (Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)) < Nat.card D := by
      have h1 := card_walkup G x
      have h2 := card_walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)
      omega
    obtain ⟨k, hk⟩ := h.minimal ((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x))
      ⟨⟨⟨hpl2, hbH⟩, hplainH⟩, hpcH⟩ hlt
    -- transport the colouring back
    obtain ⟨K, hKdef⟩ : ∃ K : D → Color, ∀ y : D, K y =
        if hy : ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x), G.CFace y w.val.val
        then k hy.choose else (if y = x then Color.c1 else Color.c0) :=
      ⟨_, fun _ => rfl⟩
    have hK1 : ∀ (y : D) (w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x)),
        G.CFace y w.val.val → K y = k w := by
      intro y w hw
      rw [hKdef y]
      split
      · rename_i hy
        exact hk.cface ((hF hy.choose w).mpr (hy.choose_spec.symm.trans hw))
      · rename_i hy
        exact absurd ⟨w, hw⟩ hy
    have hmem : ∀ z : D, (¬ ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x),
        G.CFace z w.val.val) → z = x ∨ z = n := by
      intro z hz
      by_contra hcon
      push Not at hcon
      exact hz ⟨⟨⟨z, hcon.1⟩, fun hh => hcon.2 (congrArg Subtype.val hh)⟩, SameCycle.refl _ _⟩
    have hK2 : ∀ y : D, (¬ ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x),
        G.CFace y w.val.val) → G.face y = y := by
      intro y hy
      have hfy : ¬ ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x),
          G.CFace (G.face y) w.val.val := by
        rintro ⟨w, hw⟩
        exact hy ⟨w, (G.cface_face y).trans hw⟩
      rcases hmem y hy with hyx | hyn
      · rcases hmem (G.face y) hfy with hfx | hfx
        · exact hfx.trans hyx.symm
        · rw [hyx] at hfx
          exact absurd ((hcf _ _ hfen).trans (hcf _ _ hfx)).symm (hb n)
      · rcases hmem (G.face y) hfy with hfx | hfx
        · rw [hyn] at hfx
          exact absurd ((hcf _ _ hfex).trans (hcf _ _ hfx)).symm (hb x)
        · exact hfx.trans hyn.symm
    have hcrossK : G.edge x = n → K x = Color.c1 ∧ K n = Color.c0 := by
      intro hcross
      have hen' : G.edge n = x := by
        have h6 := congrArg (G.edge : D → D) hcross
        rw [hp.edge_edge] at h6
        exact h6.symm
      have hfx : G.face x = x := by rw [hen'] at hfen; exact hfen
      have hfn : G.face n = n := by rw [hcross] at hfex; exact hfex
      have hnox : ¬ ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x),
          G.CFace x w.val.val := by
        rintro ⟨w, hw⟩
        exact w.val.property (hw.symm.eq_of_right hfx)
      have hnon : ¬ ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x),
          G.CFace n w.val.val := by
        rintro ⟨w, hw⟩
        exact w.property (Subtype.ext (hw.symm.eq_of_right hfn))
      constructor
      · rw [hKdef x]
        split
        · rename_i hh
          exact absurd hh hnox
        · simp
      · rw [hKdef n]
        split
        · rename_i hh
          exact absurd hh hnon
        · simp
    refine h.noncolorable ⟨K, ⟨?_, ?_⟩⟩
    · have hmain : ∀ y : D, y ≠ x → y ≠ n → K (G.edge y) ≠ K y := by
        intro y hy1 hy2
        have hy2' : (⟨y, hy1⟩ : Walkup G x) ≠ ⟨n, hxn⟩ :=
          fun hh => hy2 (congrArg Subtype.val hh)
        have hKy : K y = k ⟨⟨y, hy1⟩, hy2'⟩ := hK1 y _ (SameCycle.refl _ _)
        have hEy : ((((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).edge
            ⟨⟨y, hy1⟩, hy2'⟩)).val.val = walkupEdge2 G x n y := hE ⟨⟨y, hy1⟩, hy2'⟩
        have hKe : K (G.edge y) = k (((G.walkupE x).walkupE (⟨n, hxn⟩ : Walkup G x)).edge
            ⟨⟨y, hy1⟩, hy2'⟩) := by
          refine hK1 (G.edge y) _ ?_
          rw [hEy]
          by_cases hc1 : y = G.edge n
          · rw [hc1, walkupEdge2_edge_n, hp.edge_edge]
            exact (hcf _ _ hfex).symm
          · by_cases hc2 : y = G.edge x
            · rw [hc2, walkupEdge2_edge_x G hxn, hp.edge_edge]
              exact (hcf _ _ hfen).symm
            · rw [walkupEdge2_other G hc1 hc2]
        rw [hKe, hKy]
        exact hk.edge _
      intro y
      by_cases hy1 : y = x
      · by_cases he2 : G.edge y = n
        · have hcross : G.edge x = n := by rw [← hy1]; exact he2
          obtain ⟨hKx, hKn⟩ := hcrossK hcross
          rw [hy1, hcross, hKn, hKx]
          decide
        · by_cases he1 : G.edge y = x
          · exact absurd (he1.trans hy1.symm) (hp.edge_ne y)
          · have h9 := hmain (G.edge y) he1 he2
            rw [hp.edge_edge] at h9
            exact fun hc => h9 hc.symm
      · by_cases hy2 : y = n
        · by_cases he1 : G.edge y = x
          · have hen'' : G.edge n = x := by rw [← hy2]; exact he1
            have hcross : G.edge x = n := by
              have h6 := congrArg (G.edge : D → D) hen''
              rw [hp.edge_edge] at h6
              exact h6.symm
            obtain ⟨hKx, hKn⟩ := hcrossK hcross
            rw [hy2, hen'', hKx, hKn]
            decide
          · by_cases he2 : G.edge y = n
            · exact absurd (he2.trans hy2.symm) (hp.edge_ne y)
            · have h9 := hmain (G.edge y) he1 he2
              rw [hp.edge_edge] at h9
              exact fun hc => h9 hc.symm
        · exact hmain y hy1 hy2
    · intro y
      by_cases hy : ∃ w : Walkup (G.walkupE x) (⟨n, hxn⟩ : Walkup G x), G.CFace y w.val.val
      · obtain ⟨w, hw⟩ := hy
        rw [hK1 (G.face y) w ((G.cface_face y).symm.trans hw), hK1 y w hw]
      · rw [hK2 y hy]
  refine cubic_iff.mpr ⟨fun y => ?_, fun y => ?_⟩
  · have h3 : (G.node : D → D)^[3] y = y := by
      rw [← key y]
      exact Function.iterate_minimalPeriod
    exact h3
  · intro hc
    have h1 := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hc
    rw [key y] at h1
    omega

end MinimalCubic

/-! ### Configuration maps: the geometrical requirements -/

section Embeddable

variable (G)

/-- A dart has good ring arity when its face has between three and six darts.
It is easier to check the embedding of a configuration whose perimeter satisfies
this condition in an internally 6-connected map. -/
def GoodRingArity (x : D) : Prop := 3 ≤ G.arity x ∧ G.arity x ≤ 6

/-- `x` and `y` are both adjacent to a common dart of `A`.  When `A` is
face-closed and contains `x` and `y`, this says that the face at `y` is at
distance two from the face at `x` inside `A`. -/
def AtRadius2 (A : Set D) (x y : D) : Prop := ∃ z ∈ A, G.Adj x z ∧ G.Adj y z

/-- `A` has radius two: one of its darts reaches every dart of `A` in two
adjacency hops through `A`. -/
def Radius2 (A : Set D) : Prop := ∃ x ∈ A, ∀ y ∈ A, G.AtRadius2 A x y

variable {G}

/-- Being at radius two is a symmetric relation. -/
theorem AtRadius2.symm {A : Set D} {x y : D} (h : G.AtRadius2 A x y) :
    G.AtRadius2 A y x := by
  obtain ⟨z, hz, hx, hy⟩ := h
  exact ⟨z, hz, hy, hx⟩

/-- The face reading of `Hypermap.AtRadius2` used in the reference: `x` and `y`
have darts `x'`, `y'` in their faces with `edge x'` in `A` and `edge x'`,
`edge y'` in a common face. -/
theorem atRadius2_iff {A : Set D} (hA : ∀ z : D, G.face z ∈ A ↔ z ∈ A) {x y : D} :
    G.AtRadius2 A x y ↔ ∃ x' y', G.CFace x x' ∧ G.CFace y y' ∧ G.edge x' ∈ A ∧
      G.CFace (G.edge x') (G.edge y') := by
  have hclosed : ∀ {u v : D}, G.CFace u v → (u ∈ A ↔ v ∈ A) := by
    intro u v huv
    exact (congr_of_sameCycle (F := fun z : D => z ∈ A) (fun z => propext (hA z)) huv).to_iff
  constructor
  · rintro ⟨z, hz, ⟨x', hx', hxz⟩, ⟨y', hy', hyz⟩⟩
    exact ⟨x', y', hx', hy', (hclosed hxz).mpr hz, hxz.trans hyz.symm⟩
  · rintro ⟨x', y', hx', hy', hmem, hxy⟩
    exact ⟨G.edge x', hmem, ⟨x', hx', SameCycle.refl _ _⟩, ⟨y', hy', hxy.symm⟩⟩

variable (G)

/-- An embeddable configuration map with perimeter `r`: a planar, bridgeless,
connected, plain and `r`-quasicubic map whose perimeter is a face-simple
N-cycle of good ring arity, and whose kernel has radius two. -/
structure Embeddable (r : List D) : Prop where
  /-- The geometry of a configuration map with perimeter `r`. -/
  base : G.ScyclePlanarBridgelessPlainQuasicubicConnected r
  /-- The faces along the perimeter have between three and six darts. -/
  ringArity : ∀ x ∈ r, G.GoodRingArity x
  /-- The kernel of the perimeter has radius two. -/
  kernel : G.Radius2 {x | G.Kernel r x}

end Embeddable

/-! ### Configuration maps: the contract requirements -/

section Contract

variable (G)

/-- `p` is node-simple: no two of its darts lie on a common node. -/
def Sparse (p : List D) : Prop := p.Pairwise fun x y => ¬ G.CNode x y

variable {G}

/-- Node-simplicity is face-simplicity in the `permF` hypermap, which is how the
reference defines it; all the face-simplicity lemmas therefore apply. -/
theorem sparse_iff_simple_permF {p : List D} : G.Sparse p ↔ G.permF.Simple p := Iff.rfl

/-- The empty list is node-simple. -/
@[simp] theorem sparse_nil : G.Sparse ([] : List D) := List.Pairwise.nil

/-- A list with a head is node-simple exactly when its head shares no node with
its tail, which is itself node-simple. -/
theorem sparse_cons {x : D} {p : List D} :
    G.Sparse (x :: p) ↔ (∀ y ∈ p, ¬ G.CNode x y) ∧ G.Sparse p := List.pairwise_cons

/-- Node-simplicity is invariant under permutation of the list. -/
theorem Sparse.perm {p q : List D} (h : G.Sparse p) (hpq : p.Perm q) : G.Sparse q :=
  sparse_iff_simple_permF.mpr ((sparse_iff_simple_permF.mp h).perm hpq)

/-- Node-simplicity does not depend on the order of two concatenated parts. -/
theorem sparse_append_comm {p q : List D} : G.Sparse (p ++ q) ↔ G.Sparse (q ++ p) :=
  ⟨fun h => h.perm (List.perm_append_comm), fun h => h.perm (List.perm_append_comm)⟩

/-- Node-simplicity does not depend on the order of the first two of three
concatenated parts. -/
theorem sparse_append_comm_assoc {p q s : List D} :
    G.Sparse (p ++ q ++ s) ↔ G.Sparse (q ++ p ++ s) :=
  ⟨fun h => h.perm (List.Perm.append_right _ List.perm_append_comm),
   fun h => h.perm (List.Perm.append_right _ List.perm_append_comm)⟩

/-- Rotating a list preserves node-simplicity. -/
@[simp] theorem sparse_rotate {p : List D} {n : ℕ} : G.Sparse (p.rotate n) ↔ G.Sparse p :=
  ⟨fun h => h.perm (List.rotate_perm p n), fun h => h.perm (List.rotate_perm p n).symm⟩

variable (G)

/-- The darts in the face of `x` whose E-link lands in the band of `p`.  The
faces of these darts are the faces around the face of `x` that meet `p`. -/
def triadSet (p : List D) (x : D) : Set D := {y | G.CFace x y ∧ G.Fband p (G.edge y)}

/-- `x` is a triad for `p`: at least three of the faces around the face of `x`
meet `p`, but some dart of `p` is not adjacent to `x`. -/
structure Triad (p : List D) (x : D) : Prop where
  /-- At least three of the faces around the face of `x` meet `p`. -/
  three_le : 3 ≤ (G.triadSet p x).ncard
  /-- Not every dart of `p` is adjacent to `x`. -/
  not_adj : ∃ y ∈ p, ¬ G.Adj x y

variable {G}

/-- The triad set only depends on the face of a dart. -/
theorem triadSet_congr {p : List D} {x y : D} (h : G.CFace x y) :
    G.triadSet p x = G.triadSet p y := by
  ext z
  exact and_congr_left fun _ => ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- Being a triad only depends on the face of a dart. -/
theorem Triad.congr {p : List D} {x y : D} (h : G.CFace x y) (ht : G.Triad p x) :
    G.Triad p y where
  three_le := by rw [← triadSet_congr h]; exact ht.three_le
  not_adj := by
    obtain ⟨z, hz, hnz⟩ := ht.not_adj
    exact ⟨z, hz, fun hc => hnz ((adj_congr_left h z).mpr hc)⟩

variable (G)

/-- `cc` is a valid contract for the ring `r`: it has at most four darts, and
its edge closure avoids `r`, is node-simple, and has a triad in the kernel of
`r` when `cc` has four darts. -/
structure ValidContract (r cc : List D) : Prop where
  /-- The edge closure of the contract avoids the ring. -/
  off_ring : ∀ x ∈ G.insertE cc, x ∉ r
  /-- The edge closure of the contract is node-simple. -/
  sparse : G.Sparse (G.insertE cc)
  /-- The contract is nonempty. -/
  one_le_size : 1 ≤ cc.length
  /-- The contract has at most four darts. -/
  size_le : cc.length ≤ 4
  /-- A contract of four darts has a triad in the kernel of the ring. -/
  triad : cc.length = 4 → ∃ x, G.Kernel r x ∧ G.Triad (G.insertE cc) x

/-- `G` is C-reducible with contract `cc` for the ring `r`: `cc` is valid, and
every contract ring trace for `cc` lies in the Kempe coclosure of the ring
traces of colourings of `G`.  This means `G` cannot be embedded in a minimal
counter-example: contracting `cc` would give a smaller, hence four-colourable,
map whose colouring could be adjusted by Kempe flips to match a colouring
of `G`. -/
structure CReducible (r cc : List D) : Prop where
  /-- The contract is valid for the ring. -/
  base : G.ValidContract r cc
  /-- Contract ring traces are in the Kempe coclosure of the ring traces. -/
  coclosure : ∀ et : List Color, G.CcRingTrace cc r.reverse et →
    KempeCoclosure (G.RingTrace r.reverse) et

end Contract

/-! ### Preembeddings

The partial hypermap morphism built by the quiz development and extended to a
full embedding in the embedding development.  It is only defined on the kernel
of a configuration; there it must be a strict morphism for `face` and for arity,
and the darts at which it commutes with `edge` must form an `Rlink`-connected
cover of the kernel, up to faces. -/

section Preembedding

variable {D' : Type*} (G) (G' : Hypermap D') (f : D → D')

/-- `f` commutes with `edge` at `x`. -/
def EdgeCentral (x : D) : Prop := f (G.edge x) = G'.edge (f x)

/-- `f` is a preembedding on `A`: on `A` it commutes with `face` and preserves
arity, every dart of `A` shares a face with an edge-central dart, and the
edge-central darts of `A` are `Rlink`-connected. -/
structure Preembedding (A : Set D) : Prop where
  /-- On `A`, `f` commutes with `face`. -/
  face : ∀ x ∈ A, f (G.face x) = G'.face (f x)
  /-- On `A`, `f` preserves arity. -/
  arity : ∀ x ∈ A, G'.arity (f x) = G.arity x
  /-- Every dart of `A` shares a face with an edge-central dart. -/
  cover : ∀ x ∈ A, ∃ z, G.CFace x z ∧ EdgeCentral G G' f z
  /-- The edge-central darts of `A` are `Rlink`-connected. -/
  rlinked : G.RlinkConnected {x | x ∈ A ∧ EdgeCentral G G' f x}

variable {G G' f}

/-- Between plain hypermaps, `f` commutes with `edge` at `x` exactly when it
commutes with `edge` at `edge x`. -/
theorem edgeCentral_edge (hp : G.Plain) (hp' : G'.Plain) (x : D) :
    EdgeCentral G G' f (G.edge x) ↔ EdgeCentral G G' f x := by
  simp only [EdgeCentral]
  constructor
  · intro hc
    rw [hp.edge_edge] at hc
    have h1 := congrArg (G'.edge : D' → D') hc
    rw [hp'.edge_edge] at h1
    exact h1.symm
  · intro hc
    rw [hp.edge_edge]
    have h1 := congrArg (G'.edge : D' → D') hc
    rw [hp'.edge_edge] at h1
    exact h1.symm

/-- From a dart whose edge lies in a face-closed set `A` to any dart of `A`
there is a simple `Rlink` path through edge-central darts of `A`: the reference's
`preembedding_simple_path`. -/
theorem Preembedding.simple_path [Finite D] {A : Set D} (h : Preembedding G G' f A)
    (hA : ∀ x y : D, G.CFace x y → x ∈ A → y ∈ A) {x y : D}
    (hex : G.edge x ∈ A) (hy : y ∈ A) :
    ∃ p : List D, p ≠ [] ∧ List.IsChain G.Rlink (x :: p) ∧
      G.CFace (p.getLastD x) y ∧ G.Simple p ∧
      ∀ w ∈ p, w ∈ A ∧ EdgeCentral G G' f w := by
  -- an edge-central dart in the face of `edge x`, and one in the face of `y`
  obtain ⟨z, hxz, hzc⟩ := h.cover _ hex
  obtain ⟨t, hyt, htc⟩ := h.cover _ hy
  have hzA : z ∈ A := hA _ _ hxz hex
  have htA : t ∈ A := hA _ _ hyt hy
  obtain ⟨p, hchain, hpA⟩ := h.rlinked z ⟨hzA, hzc⟩ t ⟨htA, htc⟩
  -- the path starts at `x` just as well, since `edge x` and `z` share a face
  have hchain' : List.IsChain G.Rlink (x :: (p ++ [t])) := by
    obtain ⟨hhead, htail⟩ := List.isChain_cons.mp hchain
    refine List.isChain_cons.mpr ⟨fun w hw => ?_, htail⟩
    have hw' := hhead w hw
    have hz : G.edge (G.node (G.face z)) = z := G.faceK z
    have : G.CFace z w := by
      have : G.Rlink (G.node (G.face z)) w := hw'
      rwa [Rlink, hz] at this
    exact hxz.trans this
  -- cut the loops out
  obtain ⟨q, hq, hqsimple, hqlast, hqnil, hqsub⟩ := exists_simple_rlink hchain'
  have hpne : p ++ [t] ≠ [] := by simp
  refine ⟨q, fun hc => hpne (hqnil.mp hc), hq, ?_, hqsimple, ?_⟩
  · -- the path ends in the face of `y`
    have h1 : (x :: q).getLast? = some (q.getLastD x) := getLast?_cons_eq_some x q
    have h2 : (x :: (p ++ [t])).getLast? = some ((p ++ [t]).getLastD x) :=
      getLast?_cons_eq_some x (p ++ [t])
    have h3 : (p ++ [t]).getLastD x = t := getLastD_append_cons x t p []
    rw [h1, h2, h3] at hqlast
    have h4 : q.getLastD x = t := by
      exact Option.some_injective _ hqlast
    rw [h4]
    exact hyt.symm
  · intro w hw
    rcases List.mem_append.mp (hqsub w hw) with hwp | hwt
    · exact hpA w hwp
    · rw [List.mem_singleton.mp hwt]
      exact ⟨htA, htc⟩

end Preembedding

end Hypermap

end FourColor

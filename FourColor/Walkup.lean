import FourColor.Hypermap
import FourColor.Component

/-!
# The Walkup construction

Deleting a dart `z` from a hypermap suppresses `z` from two of the three
permutations (using `skip`); the third then needs a more complex adjustment to
restore the triangular identity.  Because of this asymmetry there are three
variants, and all three are used later: `walkupE` in the cube construction,
`walkupN` for Kempe chains, and `walkupF` for contraction.

Since the triangular identity determines any one permutation from the other two,
`walkupE` is well-formed by construction: its edge permutation is *defined* as
`(node' * face')⁻¹`.  What the reference proves as a well-definedness obligation
(`skip_edgeK`) appears here as `walkupE_edge_val`, the explicit formula for that
inverse, which is what the later cycle analysis actually needs.

## Main definitions

* `Hypermap.walkupE G z` — delete `z`, skipping it in `node` and `face`.
* `Hypermap.walkupN`, `Hypermap.walkupF` — the other two variants, obtained by
  conjugating `walkupE` with the rotations `permN` and `permF`.

## References

Gonthier's `theories/proof/walkup.v`.
-/

namespace FourColor

open Equiv Equiv.Perm

namespace Hypermap

variable {D : Type*} [DecidableEq D] (G : Hypermap D) (z : D)

/-- The dart type of a Walkup transform. -/
abbrev Walkup (_G : Hypermap D) (z : D) : Type _ := {x : D // x ≠ z}

/-- The Walkup construction: delete the dart `z`, skipping it in `node` and
`face`.  The edge permutation is forced by the triangular identity. -/
def walkupE : Hypermap (Walkup G z) where
  edge := (skip G.node z * skip G.face z)⁻¹
  node := skip G.node z
  face := skip G.face z
  node_face_edge := mul_inv_cancel _

@[simp] theorem walkupE_node : (G.walkupE z).node = skip G.node z := rfl
@[simp] theorem walkupE_face : (G.walkupE z).face = skip G.face z := rfl
@[simp] theorem walkupE_edge_def :
    (G.walkupE z).edge = (skip G.node z * skip G.face z)⁻¹ := rfl

/-- The Walkup variant that keeps `edge` and `face`, adjusting `node`. -/
def walkupN : Hypermap (Walkup G z) := (G.permN.walkupE z).permF

/-- The Walkup variant that keeps `edge` and `node`, adjusting `face`. -/
def walkupF : Hypermap (Walkup G z) := (G.permF.walkupE z).permN

@[simp] theorem walkupN_edge : (G.walkupN z).edge = skip G.edge z := rfl
@[simp] theorem walkupN_face : (G.walkupN z).face = skip G.face z := rfl
@[simp] theorem walkupF_edge : (G.walkupF z).edge = skip G.edge z := rfl
@[simp] theorem walkupF_node : (G.walkupF z).node = skip G.node z := rfl

/-! ### The adjusted edge permutation -/

/-- The explicit formula for the edge permutation of `walkupE`. -/
def skipEdgeFun (G : Hypermap D) (z x : D) : D :=
  if G.edge z = z then G.edge x
  else if G.face (G.edge x) = z then G.edge z
  else if G.edge x = z then G.edge (G.node z)
  else G.edge x

theorem skipEdgeFun_ne {x : D} (hx : x ≠ z) : skipEdgeFun G z x ≠ z := by
  unfold skipEdgeFun
  split
  · rename_i hez
    exact fun h => hx (G.edge.injective (h.trans hez.symm))
  · rename_i hez
    split
    · exact hez
    · rename_i h1
      split
      · rename_i h2
        intro hcon
        -- `edge (node z) = z` forces `face z = z`, contradicting `h1`
        have hk : G.edge (G.node (G.face z)) = z := G.faceK z
        have hn : G.node z = G.node (G.face z) := G.edge.injective (hcon.trans hk.symm)
        have hfz : z = G.face z := G.node.injective hn
        exact h1 (by rw [h2, ← hfz])
      · rename_i h2
        exact h2

private theorem skipFun_eq_of (f : Perm D) (z y : D) (h : f y = z) :
    skipFun f z y = f z := by simp [skipFun, h]

private theorem skipFun_ne_of (f : Perm D) (z y : D) (h : f y ≠ z) :
    skipFun f z y = f y := by simp [skipFun, h]

/-- `walkupE`'s edge permutation is the reference's `skip_edge`.  This is the
content of the reference's `skip_edgeK`. -/
theorem walkupE_edge_val (u : Walkup G z) :
    ((G.walkupE z).edge u).val = skipEdgeFun G z u.val := by
  obtain ⟨x, hx⟩ := u
  have key : skipFun G.node z (skipFun G.face z (skipEdgeFun G z x)) = x := by
    by_cases hez : G.edge z = z
    · have hwx : skipEdgeFun G z x = G.edge x := by
        simp only [skipEdgeFun]; rw [ite_eq_left hez]
      by_cases h1 : G.face (G.edge x) = z
      · have hnz : G.node z = x := by
          have h := G.edgeK x; rwa [h1] at h
        have hnfz : G.node (G.face z) = z := by
          have h := G.edgeK z; rwa [hez] at h
        rw [hwx, skipFun_eq_of _ _ _ h1, skipFun_eq_of _ _ _ hnfz, hnz]
      · rw [hwx, skipFun_ne_of _ _ _ h1, skipFun_ne_of _ _ _ (by rw [G.edgeK]; exact hx),
          G.edgeK]
    · by_cases h1 : G.face (G.edge x) = z
      · have hnz : G.node z = x := by
          have h := G.edgeK x; rwa [h1] at h
        have hwx : skipEdgeFun G z x = G.edge z := by
          simp only [skipEdgeFun]; rw [ite_eq_right hez, ite_eq_left h1]
        have hfez : G.face (G.edge z) ≠ z := by
          intro hcon
          have hnzz : G.node z = z := by
            have h := G.edgeK z; rwa [hcon] at h
          exact hx (by rw [← hnz, hnzz])
        rw [hwx, skipFun_ne_of _ _ _ hfez, skipFun_eq_of _ _ _ (G.edgeK z), hnz]
      · by_cases h2 : G.edge x = z
        · have hwx : skipEdgeFun G z x = G.edge (G.node z) := by
            simp only [skipEdgeFun]
            rw [ite_eq_right hez, ite_eq_right h1, ite_eq_left h2]
          have hnfz : G.node (G.face z) ≠ z := by
            intro hcon
            have h := G.faceK z
            rw [hcon] at h
            exact hez h
          have hval : G.node (G.face z) = x := by
            apply G.edge.injective
            rw [G.faceK, h2]
          rw [hwx, skipFun_eq_of _ _ _ (G.nodeK z), skipFun_ne_of _ _ _ hnfz, hval]
        · have hwx : skipEdgeFun G z x = G.edge x := by
            simp only [skipEdgeFun]
            rw [ite_eq_right hez, ite_eq_right h1, ite_eq_right h2]
          rw [hwx, skipFun_ne_of _ _ _ h1, skipFun_ne_of _ _ _ (by rw [G.edgeK]; exact hx),
            G.edgeK]
  have hmul : (skip G.node z * skip G.face z) ⟨skipEdgeFun G z x, skipEdgeFun_ne G z hx⟩
      = ⟨x, hx⟩ := Subtype.ext (by simpa using key)
  calc ((G.walkupE z).edge ⟨x, hx⟩).val
      = ((skip G.node z * skip G.face z)⁻¹ ⟨x, hx⟩).val := rfl
    _ = skipEdgeFun G z x := by rw [← hmul]; simp

/-! ### Size of a Walkup transform -/

omit [DecidableEq D] in
/-- A Walkup transform has exactly one dart fewer. -/
theorem card_walkup [Finite D] : Nat.card D = Nat.card (Walkup G z) + 1 := by
  have hbij : Function.Bijective (fun o : Option (Walkup G z) => o.elim z Subtype.val) := by
    constructor
    · rintro (_ | a) (_ | b) hab
      · rfl
      · exact absurd hab.symm b.2
      · exact absurd hab a.2
      · exact congrArg some (Subtype.ext hab)
    · intro x
      by_cases hx : x = z
      · exact ⟨none, hx.symm⟩
      · exact ⟨some ⟨x, hx⟩, rfl⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [Finite.card_option] at hcard
  omega


/-! ### The degenerate case

When `z` is *degenerate* — a fixed point of one of the three permutations — the
adjusted edge map collapses to a plain `skip`, and the edge orbit count then
follows from `cycleCount_skip`.
-/

/-- At a degenerate dart the adjusted edge map is just `skip`. -/
theorem skipEdgeFun_of_glink (hz : G.GLink z z) {x : D} (hx : x ≠ z) :
    skipEdgeFun G z x = skipFun G.edge z x := by
  by_cases hez : G.edge z = z
  · have hne : G.edge x ≠ z := fun hc => hx (G.edge.injective (hc.trans hez.symm))
    rw [skipEdgeFun, ite_eq_left hez, skipFun_ne_of G.edge z x hne]
  · rcases hz with h | h | h
    · exact absurd h.symm hez
    · have hnz : G.node z = z := h.symm
      have hfe : G.face (G.edge x) ≠ z := by
        intro hc
        have hk := G.edgeK x
        rw [hc, hnz] at hk
        exact hx hk.symm
      rw [skipEdgeFun, ite_eq_right hez, ite_eq_right hfe, hnz]
      rfl
    · have hfz : G.face z = z := h.symm
      have hiff : G.face (G.edge x) = z ↔ G.edge x = z :=
        ⟨fun hc => G.face.injective (hc.trans hfz.symm), fun hc => by rw [hc, hfz]⟩
      rw [skipEdgeFun, ite_eq_right hez]
      by_cases hex : G.edge x = z
      · rw [ite_eq_left (hiff.mpr hex), skipFun_eq_of G.edge z x hex]
      · rw [ite_eq_right (fun hc => hex (hiff.mp hc)), ite_eq_right hex, skipFun_ne_of G.edge z x hex]

/-- At a degenerate dart the Walkup edge permutation is `skip edge`. -/
theorem walkupE_edge_of_glink (hz : G.GLink z z) :
    (G.walkupE z).edge = skip G.edge z := by
  refine Equiv.ext fun u => Subtype.ext ?_
  rw [walkupE_edge_val, skip_val, skipEdgeFun_of_glink G z hz u.2]

/-! ### The edge orbit count away from a degenerate dart

When `z` is not degenerate the adjusted edge map is no longer a plain `skip`,
but it differs from one by a single transposition: it swaps the two values
`edge z` and `edge (node z)`, which are the images of the two darts `edge⁻¹ z`
and `node z` where the two maps disagree.  The orbit count then follows from
`cycleCount_swap_mul_of_sameCycle`, with the reference's `cross_edge` — `z` and
`node z` on a common edge orbit — deciding the direction.
-/

omit [DecidableEq D] in
theorem edge_ne_of_not_glink (hz : ¬ G.GLink z z) : G.edge z ≠ z :=
  fun h => hz (Or.inl h.symm)

omit [DecidableEq D] in
theorem node_ne_of_not_glink (hz : ¬ G.GLink z z) : G.node z ≠ z :=
  fun h => hz (Or.inr (Or.inl h.symm))

omit [DecidableEq D] in
theorem face_ne_of_not_glink (hz : ¬ G.GLink z z) : G.face z ≠ z :=
  fun h => hz (Or.inr (Or.inr h.symm))

omit [DecidableEq D] in
theorem edge_node_ne_of_not_glink (hz : ¬ G.GLink z z) : G.edge (G.node z) ≠ z := by
  intro h
  have hk : G.face (G.edge (G.node z)) = z := G.nodeK z
  rw [h] at hk
  exact face_ne_of_not_glink G z hz hk

/-- Away from a degenerate dart the adjusted edge permutation is `skip edge`
followed by the transposition of `edge z` and `edge (node z)`. -/
theorem walkupE_edge_eq_swap_mul (hz : ¬ G.GLink z z) :
    (G.walkupE z).edge
      = Equiv.swap (⟨G.edge z, edge_ne_of_not_glink G z hz⟩ : Walkup G z)
          ⟨G.edge (G.node z), edge_node_ne_of_not_glink G z hz⟩ * skip G.edge z := by
  have hez := edge_ne_of_not_glink G z hz
  have hnz := node_ne_of_not_glink G z hz
  have hfz := face_ne_of_not_glink G z hz
  have henz := edge_node_ne_of_not_glink G z hz
  set A : Walkup G z := ⟨G.edge z, hez⟩ with hA
  set B : Walkup G z := ⟨G.edge (G.node z), henz⟩ with hB
  have hAB : A ≠ B := fun h => hnz (G.edge.injective (congrArg Subtype.val h)).symm
  refine Equiv.ext fun u => Subtype.ext ?_
  obtain ⟨x, hx⟩ := u
  rw [walkupE_edge_val]
  by_cases hxe : G.edge x = z
  -- the dart `edge⁻¹ z`: `skip` steps onto `edge z`, which the swap sends to
  -- `edge (node z)`
  · have hfe : G.face (G.edge x) ≠ z := by rw [hxe]; exact hfz
    have hskip : skip G.edge z ⟨x, hx⟩ = A := Subtype.ext (skip_val_of_eq hxe)
    rw [Perm.mul_apply, hskip, Equiv.swap_apply_left, skipEdgeFun,
      ite_eq_right hez, ite_eq_right hfe, ite_eq_left hxe]
  · by_cases hxn : x = G.node z
    -- the dart `node z`: `skip` steps onto `edge (node z)`, which the swap
    -- sends back to `edge z`
    · have hfe : G.face (G.edge x) = z := by rw [hxn, G.nodeK]
      have hskip : skip G.edge z ⟨x, hx⟩ = B := by
        refine Subtype.ext ?_
        rw [skip_val_of_ne hxe]
        exact congrArg G.edge hxn
      rw [Perm.mul_apply, hskip, Equiv.swap_apply_right, skipEdgeFun,
        ite_eq_right hez, ite_eq_left hfe]
    -- everywhere else the two maps agree, and the swap is not triggered
    · have hfe : G.face (G.edge x) ≠ z := by
        intro h
        exact hxn (by rw [← G.edgeK x, h])
      have hval : (skip G.edge z ⟨x, hx⟩).val = G.edge x := skip_val_of_ne hxe
      have hne : skip G.edge z ⟨x, hx⟩ ≠ A := by
        intro h
        exact hx (G.edge.injective (by rw [← hval, h] : G.edge x = G.edge z))
      have hne' : skip G.edge z ⟨x, hx⟩ ≠ B := by
        intro h
        exact hxn (G.edge.injective (by rw [← hval, h] : G.edge x = G.edge (G.node z)))
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne hne', skip_val_of_ne hxe,
        skipEdgeFun, ite_eq_right hez, ite_eq_right hfe, ite_eq_right hxe]

/-- The two darts where the adjusted edge map disagrees with `skip edge` lie on a
common orbit exactly when `z` and `node z` lie on a common edge orbit — the
reference's `cross_edge`. -/
theorem sameCycle_skip_edge_swap_iff [Finite D] (hz : ¬ G.GLink z z) :
    (skip G.edge z).SameCycle (⟨G.edge z, edge_ne_of_not_glink G z hz⟩ : Walkup G z)
        ⟨G.edge (G.node z), edge_node_ne_of_not_glink G z hz⟩
      ↔ G.CEdge z (G.node z) := by
  rw [sameCycle_skip]
  show G.edge.SameCycle (G.edge z) (G.edge (G.node z)) ↔ _
  rw [Equiv.Perm.sameCycle_apply_left, Equiv.Perm.sameCycle_apply_right]

/-- The edge orbit count at a degenerate dart: the easy half of the reference's
`fcard_skip_edge`. -/
theorem cycleCount_walkupE_edge_of_glink [Finite D] (hz : G.GLink z z) :
    (if G.edge z = z then 2 else 1) + cycleCount (G.walkupE z).edge
      = cycleCount G.edge + 1 := by
  rw [walkupE_edge_of_glink G z hz]
  have h := cycleCount_skip G.edge z
  by_cases hez : G.edge z = z
  · rw [ite_eq_left hez] at h ⊢
    omega
  · rw [ite_eq_right hez] at h ⊢
    omega

omit [DecidableEq D] in
theorem edge_ne_edge_node_of_not_glink (hz : ¬ G.GLink z z) :
    (⟨G.edge z, edge_ne_of_not_glink G z hz⟩ : Walkup G z)
      ≠ ⟨G.edge (G.node z), edge_node_ne_of_not_glink G z hz⟩ :=
  fun h => node_ne_of_not_glink G z hz
    (G.edge.injective (congrArg Subtype.val h)).symm

/-- When `z` and `node z` lie on a common edge orbit, deleting `z` splits that
orbit: the edge orbit count goes up by one. -/
theorem cycleCount_walkupE_edge_of_cross [Fintype D] (hz : ¬ G.GLink z z)
    (hcross : G.CEdge z (G.node z)) :
    cycleCount (G.walkupE z).edge = cycleCount G.edge + 1 := by
  rw [walkupE_edge_eq_swap_mul G z hz,
    cycleCount_swap_mul_of_sameCycle _ (edge_ne_edge_node_of_not_glink G z hz)
      ((sameCycle_skip_edge_swap_iff G z hz).mpr hcross),
    cycleCount_skip_of_ne (edge_ne_of_not_glink G z hz)]

/-- When `z` and `node z` lie on different edge orbits, deleting `z` merges
them: the edge orbit count goes down by one. -/
theorem cycleCount_walkupE_edge_of_not_cross [Fintype D] (hz : ¬ G.GLink z z)
    (hcross : ¬ G.CEdge z (G.node z)) :
    cycleCount (G.walkupE z).edge + 1 = cycleCount G.edge := by
  rw [walkupE_edge_eq_swap_mul G z hz,
    cycleCount_swap_mul_of_not_sameCycle _ (edge_ne_edge_node_of_not_glink G z hz)
      (fun h => hcross ((sameCycle_skip_edge_swap_iff G z hz).mp h)),
    cycleCount_skip_of_ne (edge_ne_of_not_glink G z hz)]

open scoped Classical in
/-- The edge orbit count of a Walkup transform, in all cases: the reference's
`fcard_skip_edge`. -/
theorem cycleCount_walkupE_edge [Fintype D] :
    (if G.GLink z z then (if G.edge z = z then 2 else 1)
      else if G.CEdge z (G.node z) then 0 else 2)
      + cycleCount (G.walkupE z).edge = cycleCount G.edge + 1 := by
  by_cases hz : G.GLink z z
  · rw [ite_eq_left hz]
    exact cycleCount_walkupE_edge_of_glink G z hz
  · rw [ite_eq_right hz]
    by_cases hcross : G.CEdge z (G.node z)
    · rw [ite_eq_left hcross, Nat.zero_add, cycleCount_walkupE_edge_of_cross G z hz hcross]
    · have h := cycleCount_walkupE_edge_of_not_cross G z hz hcross
      rw [ite_eq_right hcross]
      omega

/-! ### The component count of a Walkup transform

The Walkup link relation is not the contour relation of `G` restricted to the
remaining darts: where `G` steps onto `z`, it steps over it.  It is, however, a
`IsDeletion` of it — realised by, and realising, contour paths away from `z` —
so the component count of `G` is that of the transform with the classes of the
two darts by which `z`'s neighbourhood attaches merged.
-/

/-- The Walkup contour relation is a deletion of the contour relation at `z`. -/
theorem isDeletion_clink : IsDeletion G.Clink z (G.walkupE z).Clink where
  sound := by
    rintro u v (h | h)
    · by_cases hv : G.node v.val = z
      · have hu : u.val = G.node z := (congrArg Subtype.val h).trans (skip_val_of_eq hv)
        refine Relation.EqvGen.trans _ z _ (Relation.EqvGen.rel _ _ ?_)
          (Relation.EqvGen.rel _ _ (Or.inl hv.symm))
        rw [hu]; exact G.clink_node z
      · exact Relation.EqvGen.rel _ _
          (Or.inl ((congrArg Subtype.val h).trans (skip_val_of_ne hv)))
    · by_cases hu : G.face u.val = z
      · have hv : v.val = G.face z :=
          (congrArg Subtype.val h).symm.trans (skip_val_of_eq hu)
        exact Relation.EqvGen.trans _ z _ (Relation.EqvGen.rel _ _ (Or.inr hu))
          (Relation.EqvGen.rel _ _ (Or.inr hv.symm))
      · exact Relation.EqvGen.rel _ _
          (Or.inr ((skip_val_of_ne hu).symm.trans (congrArg Subtype.val h)))
  complete := by
    rintro u v (h | h)
    · have hv : G.node v.val ≠ z := fun hc => u.2 (h.trans hc)
      exact Relation.EqvGen.rel _ _
        (Or.inl (Subtype.ext (h.trans (skip_val_of_ne hv).symm)))
    · have hu : G.face u.val ≠ z := fun hc => v.2 (h.symm.trans hc)
      exact Relation.EqvGen.rel _ _
        (Or.inr (Subtype.ext ((skip_val_of_ne hu).trans h)))

omit [DecidableEq D] in
/-- Components are the classes of the contour relation. -/
theorem compCount_eq_card_compSetoid (G : Hypermap D) :
    G.compCount = Nat.card (Quotient (compSetoid G.Clink)) := by
  have h : G.gcompSetoid = compSetoid G.Clink :=
    Setoid.ext fun x y => (G.eqvGen_clink_iff_glink x y).symm
  rw [compCount, h]

omit [DecidableEq D] in
/-- The neighbours of `z` are its `node` and `face` images and preimages. -/
theorem attached_clink_cases {u : Walkup G z} (hu : Attached G.Clink z u.val) :
    u.val = G.face (G.edge z) ∨ u.val = G.face z ∨ u.val = G.node z
      ∨ G.face u.val = z := by
  rcases hu with (h | h) | (h | h)
  · exact Or.inl (G.node.injective ((G.edgeK z).trans h)).symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- After the deletion, `node z` is linked to the `node`-preimage of `z`. -/
theorem clink_walkupE_node {hnz : G.node z ≠ z} {hfez : G.face (G.edge z) ≠ z} :
    (G.walkupE z).Clink ⟨G.node z, hnz⟩ ⟨G.face (G.edge z), hfez⟩ :=
  Or.inl (Subtype.ext (skip_val_of_eq (G.edgeK z)).symm)

/-- After the deletion, a dart whose `face` image was `z` is linked to
`face z`. -/
theorem clink_walkupE_face {u : Walkup G z} (hu : G.face u.val = z)
    {hfz : G.face z ≠ z} : (G.walkupE z).Clink u ⟨G.face z, hfz⟩ :=
  Or.inr (Subtype.ext (skip_val_of_eq hu))

omit [DecidableEq D] in
theorem face_edge_ne_of_not_glink (hz : ¬ G.GLink z z) : G.face (G.edge z) ≠ z := by
  intro h
  have hk := G.edgeK z
  rw [h] at hk
  exact node_ne_of_not_glink G z hz hk

/-- The reference's `z_barb`: `z` is a component all by itself. -/
def ZBarb : Prop := G.edge z = z ∧ G.node z = z ∧ G.face z = z

omit [DecidableEq D] in
theorem zBarb_of_face_eq_of_node_eq (hn : G.node z = z) (hf : G.face z = z) :
    G.ZBarb z := by
  refine ⟨?_, hn, hf⟩
  have h := G.nodeK z
  rw [hn] at h
  exact G.face.injective (h.trans hf.symm)

/-- Deleting a dart that is a component of its own removes that component. -/
theorem compCount_walkupE_of_barb [Finite D] (h : G.ZBarb z) :
    G.compCount = (G.walkupE z).compCount + 1 := by
  obtain ⟨he, hn, hf⟩ := h
  rw [compCount_eq_card_compSetoid, compCount_eq_card_compSetoid]
  refine Deletion.card_comp_of_isolated ?_ (isDeletion_clink G z)
  intro y hy
  rcases hy with (hc | hc) | (hc | hc)
  · exact G.node.injective (hc.symm.trans hn.symm)
  · exact hc.symm.trans hf
  · exact hc.trans hn
  · exact G.face.injective (hc.trans hf.symm)

/-- At a degenerate dart that is not a component of its own, the neighbourhood
stays connected and the component count is unchanged. -/
theorem compCount_walkupE_of_glink [Finite D] (hz : G.GLink z z)
    (hbarb : ¬ G.ZBarb z) : G.compCount = (G.walkupE z).compCount := by
  rw [compCount_eq_card_compSetoid, compCount_eq_card_compSetoid]
  by_cases hfz : G.face z = z
  -- `face z = z`, so `z` attaches only through `node z`
  · have hnz : G.node z ≠ z := fun hn => hbarb (zBarb_of_face_eq_of_node_eq G z hn hfz)
    refine Deletion.card_comp_of_attached_single (isDeletion_clink G z)
      (a := ⟨G.node z, hnz⟩) (Or.inr (Or.inl rfl)) ?_
    intro u hu
    rcases attached_clink_cases G z hu with h | h | h | h
    · have hfez : G.face (G.edge z) ≠ z := fun hc => u.2 (h.trans hc)
      rw [show u = (⟨G.face (G.edge z), hfez⟩ : Walkup G z) from Subtype.ext h]
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (clink_walkupE_node G z))
    · exact absurd (h.trans hfz) u.2
    · rw [show u = (⟨G.node z, hnz⟩ : Walkup G z) from Subtype.ext h]
      exact Relation.EqvGen.refl _
    · exact absurd (G.face.injective (h.trans hfz.symm)) u.2
  -- `face z ≠ z`, so `z` attaches only through `face z`
  · refine Deletion.card_comp_of_attached_single (isDeletion_clink G z)
      (a := ⟨G.face z, hfz⟩) (Or.inl (Or.inr rfl)) ?_
    intro u hu
    rcases attached_clink_cases G z hu with h | h | h | h
    · rcases hz with he | hn | hf
      · rw [show u = (⟨G.face z, hfz⟩ : Walkup G z) from Subtype.ext (by rw [h, ← he])]
        exact Relation.EqvGen.refl _
      · exact absurd (h.trans (G.node.injective ((G.edgeK z).trans hn))) u.2
      · exact absurd hf.symm hfz
    · rw [show u = (⟨G.face z, hfz⟩ : Walkup G z) from Subtype.ext h]
      exact Relation.EqvGen.refl _
    · rcases hz with he | hn | hf
      · have hnfz : G.node (G.face z) = z := by
          have hk := G.edgeK z
          rw [← he] at hk
          exact hk
        rw [show u = (⟨G.node z, fun hn => u.2 (h.trans hn)⟩ : Walkup G z) from
          Subtype.ext h]
        refine Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext ?_))
        exact (skip_val_of_eq (u := (⟨G.face z, hfz⟩ : Walkup G z)) hnfz).symm
      · exact absurd (h.trans hn.symm) u.2
      · exact absurd hf.symm hfz
    · exact Relation.EqvGen.rel _ _ (clink_walkupE_face G z h)

/-- Away from a degenerate dart, the components of `G` are the components of the
transform with the two attachment classes merged. -/
theorem compCount_walkupE_of_not_glink [Finite D] (hz : ¬ G.GLink z z) :
    G.compCount = Nat.card (Quotient (Setoid.adjoin
      (compSetoid (G.walkupE z).Clink)
      ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩
      ⟨G.face z, face_ne_of_not_glink G z hz⟩)) := by
  rw [compCount_eq_card_compSetoid]
  refine Deletion.card_comp_of_attached (isDeletion_clink G z)
    (Or.inl (Or.inl (G.edgeK z).symm)) (Or.inl (Or.inr rfl)) ?_
  intro u hu
  rcases attached_clink_cases G z hu with h | h | h | h
  · refine Or.inl ?_
    rw [show u = (⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩ : Walkup G z) from
      Subtype.ext h]
    exact Relation.EqvGen.refl _
  · refine Or.inr ?_
    rw [show u = (⟨G.face z, face_ne_of_not_glink G z hz⟩ : Walkup G z) from Subtype.ext h]
    exact Relation.EqvGen.refl _
  · refine Or.inl ?_
    rw [(Subtype.ext h : u = (⟨G.node z, node_ne_of_not_glink G z hz⟩ : Walkup G z))]
    exact Relation.EqvGen.rel _ _ (clink_walkupE_node G z)
  · exact Or.inr (Relation.EqvGen.rel _ _ (clink_walkupE_face G z h))

/-! ### The Walkup dichotomy

Deleting a dart either preserves the component count or splits one component in
two; the reference calls the latter case `disconnected`.  It can only happen at
a non-degenerate dart whose edge orbit passes through `node z` — the reference's
`cross_edge` — because otherwise the deletion *merges* the two edge orbits, and
the merged orbit connects the two attachment darts.
-/

/-- The reference's `disconnected`: deleting `z` splits its component in two. -/
def Disconnected : Prop := G.compCount < (G.walkupE z).compCount

/-- At a non-degenerate dart, the component count goes up by one exactly when
the two attachment darts are disconnected after the deletion. -/
theorem compCount_walkupE_of_not_glink_of_not_eqvGen [Finite D] (hz : ¬ G.GLink z z)
    (h : ¬ Relation.EqvGen (G.walkupE z).Clink
      ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩
      ⟨G.face z, face_ne_of_not_glink G z hz⟩) :
    G.compCount + 1 = (G.walkupE z).compCount := by
  rw [compCount_walkupE_of_not_glink G z hz, compCount_eq_card_compSetoid,
    ← Setoid.card_quotient_adjoin_of_not (r := compSetoid (G.walkupE z).Clink) h]

theorem compCount_walkupE_of_not_glink_of_eqvGen [Finite D] (hz : ¬ G.GLink z z)
    (h : Relation.EqvGen (G.walkupE z).Clink
      ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩
      ⟨G.face z, face_ne_of_not_glink G z hz⟩) :
    G.compCount = (G.walkupE z).compCount := by
  rw [compCount_walkupE_of_not_glink G z hz, compCount_eq_card_compSetoid,
    Setoid.adjoin_eq_self_of (r := compSetoid (G.walkupE z).Clink) h]

/-- At a non-degenerate dart with no crossing edge orbit, the two attachment
darts stay connected: the deletion merges the edge orbits of `z` and `node z`
into one, which joins them. -/
theorem eqvGen_clink_walkupE_of_not_cross [Fintype D] (hz : ¬ G.GLink z z)
    (hcross : ¬ G.CEdge z (G.node z)) :
    Relation.EqvGen (G.walkupE z).Clink
      ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩
      ⟨G.face z, face_ne_of_not_glink G z hz⟩ := by
  have hez := edge_ne_of_not_glink G z hz
  have henz := edge_node_ne_of_not_glink G z hz
  set A : Walkup G z := ⟨G.edge z, hez⟩ with hA
  set B : Walkup G z := ⟨G.edge (G.node z), henz⟩ with hB
  -- the two edge orbits merge, so `A` and `B` share an edge orbit of the
  -- transform
  have hmerge : (G.walkupE z).edge.SameCycle A B := by
    rw [walkupE_edge_eq_swap_mul G z hz,
      sameCycle_swap_mul_iff _ (edge_ne_edge_node_of_not_glink G z hz)]
    exact fun h => hcross ((sameCycle_skip_edge_swap_iff G z hz).mp h)
  have hAB : Relation.EqvGen (G.walkupE z).Clink A B :=
    ((G.walkupE z).eqvGen_clink_iff_glink A B).mpr
      ((G.walkupE z).eqvGen_glink_of_sameCycle_edge hmerge)
  -- `A` is linked to the first attachment dart, `B` to the second
  have hAa : (G.walkupE z).Clink A ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩ :=
    Or.inr (Subtype.ext (skip_val_of_ne (u := A) (face_edge_ne_of_not_glink G z hz)))
  have hBb : (G.walkupE z).Clink B ⟨G.face z, face_ne_of_not_glink G z hz⟩ :=
    Or.inr (Subtype.ext (skip_val_of_eq (u := B) (G.nodeK z)))
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hAa))
    (Relation.EqvGen.trans _ _ _ hAB (Relation.EqvGen.rel _ _ hBb))

/-- A splitting dart is non-degenerate and has a crossing edge orbit: the
reference's `disconnected_cross_edge`. -/
theorem not_glink_and_cross_of_disconnected [Fintype D] (h : G.Disconnected z) :
    ¬ G.GLink z z ∧ G.CEdge z (G.node z) := by
  by_cases hz : G.GLink z z
  · by_cases hbarb : G.ZBarb z
    · exact absurd (compCount_walkupE_of_barb G z hbarb) (by
        simp only [Disconnected] at h; omega)
    · exact absurd (compCount_walkupE_of_glink G z hz hbarb) (by
        simp only [Disconnected] at h; omega)
  · refine ⟨hz, ?_⟩
    by_contra hcross
    exact absurd (compCount_walkupE_of_not_glink_of_eqvGen G z hz
      (eqvGen_clink_walkupE_of_not_cross G z hz hcross)) (by
        simp only [Disconnected] at h; omega)

open scoped Classical in
/-- The contribution of the deleted dart to the Euler formula: the reference's
`n_comp_z`, whose argument is `Disconnected` on the left-hand side of the
formula and `CEdge z (node z)` on the right. -/
noncomputable def zComp (b : Prop) : ℕ :=
  if G.GLink z z then (if G.ZBarb z then 2 else 1) else if b then 0 else 1

/-- The component count of a Walkup transform, in all cases: the reference's
`n_comp_glink_Walkup`. -/
theorem compCount_walkupE [Fintype D] :
    G.zComp z (G.Disconnected z) + (G.walkupE z).compCount = G.compCount + 1 := by
  simp only [zComp]
  by_cases hz : G.GLink z z
  · have hnd : ¬ G.Disconnected z := fun hd => (not_glink_and_cross_of_disconnected G z hd).1 hz
    rw [ite_eq_left hz]
    by_cases hbarb : G.ZBarb z
    · rw [ite_eq_left hbarb, compCount_walkupE_of_barb G z hbarb]
      omega
    · rw [ite_eq_right hbarb, compCount_walkupE_of_glink G z hz hbarb]
      omega
  · rw [ite_eq_right hz]
    by_cases hcon : Relation.EqvGen (G.walkupE z).Clink
        ⟨G.face (G.edge z), face_edge_ne_of_not_glink G z hz⟩
        ⟨G.face z, face_ne_of_not_glink G z hz⟩
    · have he := compCount_walkupE_of_not_glink_of_eqvGen G z hz hcon
      have hnd : ¬ G.Disconnected z := by simp only [Disconnected]; omega
      rw [ite_eq_right hnd]
      omega
    · have he := compCount_walkupE_of_not_glink_of_not_eqvGen G z hz hcon
      have hd : G.Disconnected z := by simp only [Disconnected]; omega
      rw [ite_eq_left hd]
      omega

/-! ### The Euler formula and the genus

Both sides of the Euler formula lose the same amount when a dart is deleted, up
to the contribution `zComp` of the deleted dart, which is measured by
`Disconnected` on the left and by `CEdge z (node z)` on the right.  Since a
splitting dart always has a crossing edge orbit, the right-hand contribution is
never the larger one, and the genus can only drop.
-/

omit [DecidableEq D] in
theorem zBarb_of_edge_eq_of_node_eq (he : G.edge z = z) (hn : G.node z = z) :
    G.ZBarb z := by
  refine ⟨he, hn, ?_⟩
  have h := G.edgeK z
  rw [he] at h
  exact G.node.injective (h.trans hn.symm)

omit [DecidableEq D] in
theorem zBarb_of_edge_eq_of_face_eq (he : G.edge z = z) (hf : G.face z = z) :
    G.ZBarb z := by
  refine ⟨he, ?_, hf⟩
  have h := G.edgeK z
  rw [he, hf] at h
  exact h

theorem two_mul_zComp_add_eulerLhs [Fintype D] :
    2 * G.zComp z (G.Disconnected z) + (G.walkupE z).EulerLhs = G.EulerLhs + 1 := by
  have hcard := card_walkup G z
  have hcomp := compCount_walkupE G z
  simp only [EulerLhs]
  omega

theorem two_mul_zComp_add_eulerRhs [Fintype D] :
    2 * G.zComp z (G.CEdge z (G.node z)) + (G.walkupE z).EulerRhs = G.EulerRhs + 1 := by
  have hnode := cycleCount_skip G.node z
  have hface := cycleCount_skip G.face z
  simp only [EulerRhs, zComp, walkupE_node, walkupE_face]
  by_cases hz : G.GLink z z
  · rw [ite_eq_left hz]
    have hedge := cycleCount_walkupE_edge_of_glink G z hz
    by_cases hbarb : G.ZBarb z
    · obtain ⟨he, hn, hf⟩ := id hbarb
      rw [ite_eq_left hbarb]
      rw [ite_eq_left he] at hedge
      rw [ite_eq_left hn] at hnode
      rw [ite_eq_left hf] at hface
      omega
    · rw [ite_eq_right hbarb]
      have h1 : G.edge z = z ∨ G.node z = z ∨ G.face z = z := by
        rcases hz with h | h | h
        exacts [Or.inl h.symm, Or.inr (Or.inl h.symm), Or.inr (Or.inr h.symm)]
      rcases h1 with he | hn | hf
      · have hn' : G.node z ≠ z := fun h => hbarb (zBarb_of_edge_eq_of_node_eq G z he h)
        have hf' : G.face z ≠ z := fun h => hbarb (zBarb_of_edge_eq_of_face_eq G z he h)
        rw [ite_eq_left he] at hedge
        rw [ite_eq_right hn'] at hnode
        rw [ite_eq_right hf'] at hface
        omega
      · have he' : G.edge z ≠ z := fun h => hbarb (zBarb_of_edge_eq_of_node_eq G z h hn)
        have hf' : G.face z ≠ z := fun h => hbarb (zBarb_of_face_eq_of_node_eq G z hn h)
        rw [ite_eq_right he'] at hedge
        rw [ite_eq_left hn] at hnode
        rw [ite_eq_right hf'] at hface
        omega
      · have he' : G.edge z ≠ z := fun h => hbarb (zBarb_of_edge_eq_of_face_eq G z h hf)
        have hn' : G.node z ≠ z := fun h => hbarb (zBarb_of_face_eq_of_node_eq G z h hf)
        rw [ite_eq_right he'] at hedge
        rw [ite_eq_right hn'] at hnode
        rw [ite_eq_left hf] at hface
        omega
  · rw [ite_eq_right hz]
    rw [ite_eq_right (node_ne_of_not_glink G z hz)] at hnode
    rw [ite_eq_right (face_ne_of_not_glink G z hz)] at hface
    by_cases hcross : G.CEdge z (G.node z)
    · rw [ite_eq_left hcross]
      have hedge := cycleCount_walkupE_edge_of_cross G z hz hcross
      omega
    · rw [ite_eq_right hcross]
      have hedge := cycleCount_walkupE_edge_of_not_cross G z hz hcross
      omega

/-- The right-hand contribution of the deleted dart never exceeds the left-hand
one, because a splitting dart always has a crossing edge orbit. -/
theorem zComp_cross_le_zComp_disconnected [Fintype D] :
    G.zComp z (G.CEdge z (G.node z)) ≤ G.zComp z (G.Disconnected z) := by
  simp only [zComp]
  by_cases hz : G.GLink z z
  · rw [ite_eq_left hz, ite_eq_left hz]
  · rw [ite_eq_right hz, ite_eq_right hz]
    by_cases hd : G.Disconnected z
    · rw [ite_eq_left hd, ite_eq_left (not_glink_and_cross_of_disconnected G z hd).2]
    · rw [ite_eq_right hd]
      by_cases hc : G.CEdge z (G.node z)
      · rw [ite_eq_left hc]
        omega
      · rw [ite_eq_right hc]

/-- Deleting a dart cannot raise the genus. -/
theorem genus_walkupE_le [Fintype D] : (G.walkupE z).genus ≤ G.genus := by
  have hl := two_mul_zComp_add_eulerLhs G z
  have hr := two_mul_zComp_add_eulerRhs G z
  have hle := zComp_cross_le_zComp_disconnected G z
  simp only [genus]
  omega

/-- Deleting a degenerate dart, or one with no crossing edge orbit, preserves
the genus. -/
theorem genus_walkupE_eq [Fintype D] (h : G.GLink z z ∨ ¬ G.CEdge z (G.node z)) :
    (G.walkupE z).genus = G.genus := by
  have hl := two_mul_zComp_add_eulerLhs G z
  have hr := two_mul_zComp_add_eulerRhs G z
  have heq : G.zComp z (G.CEdge z (G.node z)) = G.zComp z (G.Disconnected z) := by
    simp only [zComp]
    rcases h with hz | hc
    · rw [ite_eq_left hz, ite_eq_left hz]
    · have hd : ¬ G.Disconnected z := fun hd =>
        hc (not_glink_and_cross_of_disconnected G z hd).2
      by_cases hz : G.GLink z z
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, ite_eq_right hc, ite_eq_right hd]
  simp only [genus]
  omega

/-- Deleting a dart from a planar hypermap leaves it planar. -/
theorem planar_walkupE [Fintype D] (h : G.Planar) : (G.walkupE z).Planar := by
  have := genus_walkupE_le G z
  simp only [Planar] at h ⊢
  omega

/-- The Euler formula is exact for `G` as soon as it is for the transform. -/
theorem evenGenus_walkupE [Fintype D] (h : (G.walkupE z).EvenGenus) : G.EvenGenus := by
  have hl := two_mul_zComp_add_eulerLhs G z
  have hr := two_mul_zComp_add_eulerRhs G z
  have hle := zComp_cross_le_zComp_disconnected G z
  simp only [EvenGenus, genus] at h ⊢
  omega

/-! ### Lifting contour paths to the transforms

A contour link between two darts other than `z` is a contour link of the
transform, provided the target is not the one dart where the transform's own
`node` (for `walkupN`) or `face` (for `walkupF`) steps over `z`.  Hence a
contour path avoiding `z` (and that dart) lifts to a contour path of the
transform, which is how Moebius paths are pushed into the smaller maps.
-/

@[simp] theorem walkupN_node :
    (G.walkupN z).node = (skip G.face z * skip G.edge z)⁻¹ := rfl

@[simp] theorem walkupF_face :
    (G.walkupF z).face = (skip G.edge z * skip G.node z)⁻¹ := rfl

/-- Contour links away from `z` are contour links of `walkupE`. -/
theorem clink_walkupE_of_clink {u v : Walkup G z} (h : G.Clink u.val v.val) :
    (G.walkupE z).Clink u v := by
  rcases h with h | h
  · have hv : G.node v.val ≠ z := fun hc => u.2 (h.trans hc)
    exact Or.inl (Subtype.ext (h.trans (skip_val_of_ne hv).symm))
  · have hu : G.face u.val ≠ z := fun hc => v.2 (h.symm.trans hc)
    exact Or.inr (Subtype.ext ((skip_val_of_ne hu).trans h))

/-- Contour links away from `z` and from `face z` are contour links of
`walkupN`. -/
theorem clink_walkupN_of_clink {u v : Walkup G z} (hv : v.val ≠ G.face z)
    (h : G.Clink u.val v.val) : (G.walkupN z).Clink u v := by
  rcases h with h | h
  · refine Or.inl ?_
    have hfe : G.face (G.edge u.val) = v.val := G.node.injective ((G.edgeK u.val).trans h)
    have heu : G.edge u.val ≠ z := fun hc => hv (by rw [← hfe, hc])
    have h1 : ((skip G.edge z) u).val = G.edge u.val := skip_val_of_ne heu
    have h2 : G.face ((skip G.edge z) u).val ≠ z := by rw [h1, hfe]; exact v.2
    have key : (skip G.face z * skip G.edge z) u = v :=
      Subtype.ext (by rw [Perm.mul_apply, skip_val_of_ne h2, h1, hfe])
    rw [walkupN_node, ← key]
    simp
  · have hu : G.face u.val ≠ z := fun hc => v.2 (h.symm.trans hc)
    exact Or.inr (Subtype.ext ((skip_val_of_ne hu).trans h))

/-- Contour links away from `z` and from `face (edge z)` are contour links of
`walkupF`. -/
theorem clink_walkupF_of_clink {u v : Walkup G z} (hv : v.val ≠ G.face (G.edge z))
    (h : G.Clink u.val v.val) : (G.walkupF z).Clink u v := by
  rcases h with h | h
  · have hv' : G.node v.val ≠ z := fun hc => u.2 (h.trans hc)
    exact Or.inl (Subtype.ext (h.trans (skip_val_of_ne hv').symm))
  · refine Or.inr ?_
    have hen : G.edge (G.node v.val) = u.val := G.face.injective ((G.nodeK v.val).trans h.symm)
    have hnv : G.node v.val ≠ z := by
      intro hc
      refine hv ?_
      have h0 : G.face (G.edge (G.node v.val)) = v.val := G.nodeK v.val
      rw [hc] at h0
      exact h0.symm
    have h1 : ((skip G.node z) v).val = G.node v.val := skip_val_of_ne hnv
    have h2 : G.edge ((skip G.node z) v).val ≠ z := by rw [h1, hen]; exact u.2
    have key : (skip G.edge z * skip G.node z) v = u :=
      Subtype.ext (by rw [Perm.mul_apply, skip_val_of_ne h2, h1, hen])
    rw [walkupF_face, ← key]
    simp

omit [DecidableEq D] in
/-- Lifting a chain of darts along the inclusion. -/
private theorem isChain_of_map {r : D → D → Prop} {s : Walkup G z → Walkup G z → Prop}
    {P : D → Prop} (hstep : ∀ u v : Walkup G z, P v.val → r u.val v.val → s u v)
    {l : List (Walkup G z)} (hP : ∀ u ∈ l.tail, P u.val)
    (h : List.IsChain r (l.map Subtype.val)) : List.IsChain s l := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons u l ih =>
    match l with
    | [] => exact List.IsChain.singleton u
    | v :: l =>
      rw [List.map_cons, List.map_cons, List.isChain_cons_cons] at h
      refine List.IsChain.cons_cons ?_ (ih (fun w hw => hP w (List.mem_cons_of_mem _ hw)) ?_)
      · exact hstep u v (hP v List.mem_cons_self) h.1
      · rw [List.map_cons]; exact h.2
    
/-- A contour path avoiding `z` is a contour path of `walkupE`. -/
theorem isChain_clink_walkupE {l : List (Walkup G z)}
    (h : List.IsChain G.Clink (l.map Subtype.val)) :
    List.IsChain (G.walkupE z).Clink l :=
  isChain_of_map G z (P := fun _ => True) (fun _ _ _ hr => clink_walkupE_of_clink G z hr)
    (fun _ _ => trivial) h

/-- A contour path avoiding `z` and `face z` is a contour path of `walkupN`. -/
theorem isChain_clink_walkupN {l : List (Walkup G z)}
    (hP : ∀ u ∈ l.tail, u.val ≠ G.face z)
    (h : List.IsChain G.Clink (l.map Subtype.val)) :
    List.IsChain (G.walkupN z).Clink l :=
  isChain_of_map G z (P := fun x => x ≠ G.face z)
    (fun _ _ hv hr => clink_walkupN_of_clink G z hv hr) hP h

/-- A contour path avoiding `z` and `face (edge z)` is a contour path of
`walkupF`. -/
theorem isChain_clink_walkupF {l : List (Walkup G z)}
    (hP : ∀ u ∈ l.tail, u.val ≠ G.face (G.edge z))
    (h : List.IsChain G.Clink (l.map Subtype.val)) :
    List.IsChain (G.walkupF z).Clink l :=
  isChain_of_map G z (P := fun x => x ≠ G.face (G.edge z))
    (fun _ _ hv hr => clink_walkupF_of_clink G z hv hr) hP h

/-- Deleting a dart from a planar hypermap leaves it planar, in the `walkupN`
form. -/
theorem planar_walkupN [Fintype D] (h : G.Planar) : (G.walkupN z).Planar := by
  rw [walkupN, planar_permF]
  exact planar_walkupE G.permN z ((planar_permN G).mpr h)

/-- Deleting a dart from a planar hypermap leaves it planar, in the `walkupF`
form. -/
theorem planar_walkupF [Fintype D] (h : G.Planar) : (G.walkupF z).Planar := by
  rw [walkupF, planar_permN]
  exact planar_walkupE G.permF z ((planar_permF G).mpr h)

/-- Away from the exceptional dart, `walkupN`'s node map is the original one. -/
theorem walkupN_node_eq_of {u : Walkup G z} (hnu : G.node u.val ≠ z)
    (heu : G.edge (G.node u.val) ≠ z) :
    (G.walkupN z).node u = ⟨G.node u.val, hnu⟩ := by
  have h1 : (skip G.face z * skip G.edge z) (⟨G.node u.val, hnu⟩ : Walkup G z) = u := by
    refine Subtype.ext ?_
    have h2 : ((skip G.edge z) (⟨G.node u.val, hnu⟩ : Walkup G z)).val = G.edge (G.node u.val) :=
      skip_val_of_ne heu
    have h3 : G.face ((skip G.edge z) (⟨G.node u.val, hnu⟩ : Walkup G z)).val ≠ z := by
      rw [h2, G.nodeK]
      exact u.2
    rw [Perm.mul_apply, skip_val_of_ne h3, h2, G.nodeK]
  rw [walkupN_node, Equiv.Perm.inv_eq_iff_eq]
  exact h1.symm

/-- At the exceptional dart, `walkupN`'s node map jumps over `z`. -/
theorem walkupN_node_eq_jump {u v : Walkup G z} (h1 : G.edge u.val ≠ z)
    (h2 : G.face (G.edge u.val) = z) (h3 : v.val = G.face z) :
    (G.walkupN z).node v = u := by
  have h4 : (skip G.face z * skip G.edge z) u = v := by
    refine Subtype.ext ?_
    have h5 : ((skip G.edge z) u).val = G.edge u.val := skip_val_of_ne h1
    have h6 : G.face ((skip G.edge z) u).val = z := by rw [h5]; exact h2
    rw [Perm.mul_apply, skip_val_of_eq h6, h3]
  rw [walkupN_node, Equiv.Perm.inv_eq_iff_eq]
  exact h4.symm

/-- At the dart whose `node` image is the deleted one, `walkupN`'s node map
lands on `edge z`: this is the substitution that makes the composite of the two
Walkup transforms at `z` and `edge z` swap `node (edge z)` with `node z`. -/
theorem walkupN_node_eq_edge (hee : G.edge (G.edge z) = z) {v : Walkup G z}
    (h : G.node v.val = z) (hez : G.edge z ≠ z) :
    (G.walkupN z).node v = ⟨G.edge z, hez⟩ := by
  have hv : v.val = G.face (G.edge z) := by
    have hk : G.node (G.face (G.edge z)) = z := G.edgeK z
    exact G.node.injective (h.trans hk.symm)
  have h1 : (skip G.edge z (⟨G.edge z, hez⟩ : Walkup G z)).val = G.edge z :=
    skip_val_of_eq (u := (⟨G.edge z, hez⟩ : Walkup G z)) hee
  have h2 : G.face ((skip G.edge z) (⟨G.edge z, hez⟩ : Walkup G z)).val ≠ z := by
    rw [h1, ← hv]
    exact v.2
  have hkey : (skip G.face z * skip G.edge z) (⟨G.edge z, hez⟩ : Walkup G z) = v :=
    Subtype.ext (by rw [Perm.mul_apply, skip_val_of_ne h2, h1, ← hv])
  rw [walkupN_node, Equiv.Perm.inv_eq_iff_eq]
  exact hkey.symm

/-- At the exceptional dart, `walkupF`'s face map jumps over `z`. -/
theorem walkupF_face_eq_jump {u v : Walkup G z} (h0 : G.node z ≠ z)
    (h1 : G.node v.val = z) (h2 : G.edge (G.node z) ≠ z)
    (h3 : u.val = G.edge (G.node z)) : (G.walkupF z).face u = v := by
  have h4 : (skip G.edge z * skip G.node z) v = u := by
    refine Subtype.ext ?_
    have h5 : ((skip G.node z) v).val = G.node z := skip_val_of_eq h1
    have h6 : G.edge ((skip G.node z) v).val ≠ z := by rw [h5]; exact h2
    rw [Perm.mul_apply, skip_val_of_ne h6, h5, h3]
  rw [walkupF_face, Equiv.Perm.inv_eq_iff_eq]
  exact h4.symm

end Hypermap

end FourColor

import FourColor.GridMap
import FourColor.Finitize

/-!
# Discretising a finite simple map

This is the bridge from the continuous plane to combinatorics: the port of
`discretize.v`.  Given a finite simple map `m₀` of the real plane we build a
finite hypermap whose four-colourings induce four-colourings of `m₀`, which is
exactly the hypothesis `discretize` of `fourColorTheorem_of`.

The construction proceeds in five steps.

1. **Transversal.**  `exists_map_repr` enumerates the regions of `m₀` by a
   finite family of representative points `mr : Fin Nr → Point`, one per region.
2. **Adjacency boxes.**  `exists_adjbox` chooses, for each adjacent pair of
   regions, a non-corner border point and a rectangle around it small enough
   that no third region comes near, then approximates these rectangles by grid
   rectangles at a *common* scale.  Distinct pairs get disjoint boxes.
3. **Interpolation.**  `connected_matte` is the geometric heart: inside an open
   connected region, any scaled matte can be grown to a larger scaled matte
   still inside the region and reaching any prescribed point of it.
4. **Region mattes.**  `exists_smatte` iterates the interpolation to produce,
   for each region, a scaled matte contained in it and meeting the inset of
   every adjacency box incident to it.
5. **The grid map.**  `exists_grid_map` from `FourColor/GridMap.lean` turns this
   data into a planar bridgeless hypermap, and `discretize` transports a
   four-colouring of it back to the plane.

## Main definitions

* `MrProper` — a family of points is a proper transversal of `m₀`.
* `ABMrProper` — a scaled rectangle properly witnesses an adjacency: the two
  named regions reach its inset and no other region meets it at all.
* `SMatteInterpolated` — the union of all scaled mattes interpolating between a
  region and an ambient region.
* `ProperSMatte` — a scaled matte approximating a region and meeting a
  prescribed family of adjacency box insets.

## Main results

* `exists_map_repr`, `exists_adjbox`, `connected_matte`, `exists_smatte` — the
  four preparatory steps.
* `discretize` — the discretisation theorem in the shape required by
  `fourColorTheorem_of`.

## References

Gonthier's `theories/proof/discretize.v`.
-/

namespace FourColor

open Hypermap

variable {m₀ : PlaneMap}

/-! ### Step 1: a transversal of the regions -/

/-- A *proper transversal*: each `mr i` is covered by `m₀`, and distinct indices
name points of distinct regions. -/
def MrProper (m₀ : PlaneMap) {Nr : ℕ} (mr : Fin Nr → Point) : Prop :=
  ∀ i, mr i ∈ cover m₀ ∧ ∀ j, mr j ∈ m₀ (mr i) → i = j

/-- A finite plain map has a finite proper transversal covering all its
regions. -/
theorem exists_map_repr (hm : PlainMap m₀) (hfin : ∃ n, AtMostRegions n m₀) :
    ∃ (Nr : ℕ) (mr : Fin Nr → Point), MrProper m₀ mr ∧
      ∀ z ∈ cover m₀, ∃ i, z ∈ m₀ (mr i) := by
  classical
  obtain ⟨n, f, hf⟩ := hfin
  -- Keep the least index of each region.
  set T : Finset ℕ :=
    (Finset.range n).filter (fun i => f i ∈ cover m₀ ∧ ∀ j < i, f i ∉ m₀ (f j)) with hT
  have hmemT : ∀ i, i ∈ T ↔ i < n ∧ f i ∈ cover m₀ ∧ ∀ j < i, f i ∉ m₀ (f j) := by
    intro i; rw [hT, Finset.mem_filter, Finset.mem_range]
  set E := T.equivFin with hE
  refine ⟨T.card, fun k => f ((E.symm k : {x // x ∈ T}) : ℕ), fun k => ⟨?_, ?_⟩, ?_⟩
  · exact ((hmemT _).mp (E.symm k).2).2.1
  · intro j hj
    have ha := (hmemT _).mp (E.symm k).2
    have hb := (hmemT _).mp (E.symm j).2
    have hab : ((E.symm k : {x // x ∈ T}) : ℕ) = ((E.symm j : {x // x ∈ T}) : ℕ) := by
      rcases lt_trichotomy ((E.symm k : {x // x ∈ T}) : ℕ)
          ((E.symm j : {x // x ∈ T}) : ℕ) with h | h | h
      · exact absurd hj (hb.2.2 _ h)
      · exact h
      · exact absurd (hm.symm _ _ hj) (ha.2.2 _ h)
    have : E.symm k = E.symm j := Subtype.ext hab
    exact E.symm.injective this
  · intro z hz
    obtain ⟨i, hin, hzi⟩ := hf z hz
    have hQi : f i ∈ m₀ (f i) := hm.mem_cover_left hzi
    have hex : ∃ j, f i ∈ m₀ (f j) := ⟨i, hQi⟩
    set j := Nat.find hex with hj
    have hQj : f i ∈ m₀ (f j) := Nat.find_spec hex
    have hjle : j ≤ i := Nat.find_le hQi
    have hjT : j ∈ T := by
      refine (hmemT j).mpr ⟨lt_of_le_of_lt hjle hin, hm.mem_cover_left hQj, ?_⟩
      intro c hc hcon
      exact Nat.find_min hex hc (hm.trans _ _ hcon hQj)
    refine ⟨E ⟨j, hjT⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hm.trans _ _ hQj hzi

/-! ### Step 3: interpolating mattes inside a connected region

The geometric heart of the discretisation.  Inside an open connected region `U`
any scaled matte contained in `U` can be grown, still inside `U`, so as to cover
any prescribed point of `U`.  The proof is the classical connectedness argument:
the set of points reached by some interpolating matte is open (by refining the
grid until the corner obstruction at the point vanishes) and so is its
complement in `U` (by extending a coarse matte across a whole grid rectangle);
since the first is nonempty, it is all of `U`.
-/

/-- `W` interpolates at `z` between `U` and `V`: it contains `U` and `z`, and is
contained in `V`. -/
def InterpolantAt (z : Point) (U V W : Region) : Prop :=
  z ∈ W ∧ U ⊆ W ∧ W ⊆ V

/-- The union of all scaled mattes interpolating between `U` and `V`. -/
def SMatteInterpolated (U V : Region) : Region :=
  {z | ∃ w : SMatte, InterpolantAt z U V w.toRegion}

/-- Membership in the region of a scaled matte. -/
theorem mem_smatte_toRegion {w : SMatte} {z : Point} :
    z ∈ w.toRegion ↔ ∃ p : GPoint, ApproxPoint w.scale z p ∧ p ∈ w.matte.disk :=
  Iff.rfl

/-- Membership in the region of a scaled rectangle. -/
theorem mem_srect_toRegion {b : SRect} {z : Point} :
    z ∈ b.toRegion ↔ ∃ p : GPoint, ApproxPoint b.scale z p ∧ p ∈ b.rect.toRegion :=
  Iff.rfl

/-- Membership in the inset region of a scaled rectangle. -/
theorem mem_srect_inset_toRegion {b : SRect} {z : Point} :
    z ∈ b.inset.toRegion ↔ ∃ p : GPoint, ApproxPoint b.scale z p ∧ p ∈ b.rect.inset.toRegion :=
  Iff.rfl

/-- The four pixels around a grid vertex lie among the nine pixels touching it. -/
theorem ltouch_subset_gtouch (p : GPoint) : (ltouch p).toRegion ⊆ (gtouch p).toRegion := by
  intro q hq
  simp only [ltouch, GRect.mem_toRegion] at hq
  simp only [gtouch, GRect.mem_toRegion]
  omega

/-- A rectangle is a neighbourhood of each of its points, in the elementary
sense. -/
theorem isOpenRegion_rect (r : Rect) : IsOpenRegion r.toRegion :=
  (isOpenRegion_iff _).mpr (isOpen_rect r)

/-- A region is contained in its closure. -/
theorem subset_regionClosure (r : Region) : r ⊆ regionClosure r :=
  fun z hz _ _ hzu => ⟨z, hz, hzu⟩

/-- Refining a scaled rectangle twice is refining it once by the sum. -/
theorem refineSRect_add (a b : ℕ) (r : SRect) :
    refineSRect (a + b) r = refineSRect a (refineSRect b r) := by
  simp only [refineSRect, SRect.mk.injEq]
  exact ⟨by omega, Function.iterate_add_apply _ a b _⟩

/-- The core induction behind the openness of the interpolated region: once the
corner obstruction at the approximating pixel is bounded, the point has a whole
rectangle neighbourhood of interpolated points. -/
private theorem interpolated_nhds (U : Region) (mm : SMatte) (z : Point) :
    ∀ n : ℕ, ∀ (w : SMatte) (b : SRect), b.scale = w.scale →
      z ∈ b.inset.toRegion → b.toRegion ⊆ U →
      InterpolantAt z mm.toRegion U w.toRegion →
      (∃ p : GPoint, ApproxPoint w.scale z p ∧ p ∈ w.matte.disk ∧
        mcorner w.matte p < n) →
      ∃ r : Rect, z ∈ r.toRegion ∧ r.toRegion ⊆ SMatteInterpolated mm.toRegion U := by
  intro n
  induction n with
  | zero => rintro _ _ _ _ _ _ ⟨_, _, _, h⟩; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rintro w b hbs hzb hbU ⟨hzw, hmw, hwU⟩ ⟨p, hp, hpd, hpc⟩
    by_cases hc : mcorner w.matte p = 0
    · -- No obstruction: the four pixels around `p` are already in the matte.
      obtain ⟨r, hzr, hrsub⟩ := rect_approx hp
      refine ⟨r, hzr, fun t htr => ?_⟩
      obtain ⟨q, hq, hql⟩ := hrsub htr
      exact ⟨w, ⟨q, hq, mem_disk_of_mem_ltouch hpd hc hql⟩, hmw, hwU⟩
    · -- Refine the grid once and lower the obstruction.
      have hcpos : 0 < mcorner w.matte p := Nat.pos_of_ne_zero hc
      obtain ⟨q, hq, hqi⟩ := hzb
      have hqp : q = p := approxPoint_inj (hbs ▸ hq) hp
      have hbp : p ∈ b.rect.inset.toRegion := hqp ▸ hqi
      obtain ⟨p2, hp2⟩ := approxPoint_exists (w.scale + 1) z
      have hhalf : halfg p2 = p := approxPoint_inj (approxPoint_halfg hp2) hp
      obtain ⟨xm, hx1, hx2, hx3⟩ :=
        refine_mcorner (m := w.matte) (r := b.rect) (q := p2)
          (by rw [hhalf]; exact hpd) (by rw [hhalf]; exact hbp) (by rw [hhalf]; exact hcpos)
      have hxp2 : p2 ∈ xm.disk := hx1 p2 (by rw [hhalf]; exact hpd)
      refine ih ⟨w.scale + 1, xm⟩ (refineSRect 1 b) (by simp [refineSRect, hbs]) ?_ ?_
        ⟨⟨p2, hp2, hxp2⟩, ?_, ?_⟩ ⟨p2, hp2, hxp2, ?_⟩
      · exact inset_refineSRect 1 b ⟨q, hq, hqi⟩
      · rw [toRegion_refineSRect]; exact hbU
      · intro t htm
        obtain ⟨c, hc1, hc2⟩ := hmw htm
        refine ⟨gapprox (w.scale + 1) t, approxPoint_gapprox _ _, hx1 _ ?_⟩
        rw [approxPoint_inj (approxPoint_halfg (approxPoint_gapprox (w.scale + 1) t)) hc1]
        exact hc2
      · rintro t ⟨c, hc1, hc2⟩
        rcases hx2 c hc2 with h | h
        · exact hbU ⟨halfg c, by rw [hbs]; exact approxPoint_halfg hc1, h⟩
        · exact hwU ⟨halfg c, approxPoint_halfg hc1, h⟩
      · have hlt := hx3
        rw [hhalf] at hlt
        exact hlt.trans_le (Nat.lt_succ_iff.mp hpc)

/-- The interpolated region is open. -/
private theorem isOpenRegion_smatteInterpolated {U : Region} (hU : IsOpenRegion U)
    (mm : SMatte) : IsOpenRegion (SMatteInterpolated mm.toRegion U) := by
  rintro z ⟨w, hzw, hmw, hwU⟩
  obtain ⟨r, hzr, hrU⟩ := hU z (hwU hzw)
  obtain ⟨b1, hzb1, hb1r⟩ := approx_rect hzr
  obtain ⟨p, hp, hpd⟩ : ∃ p : GPoint, ApproxPoint (refineSMatte b1.scale w).scale z p ∧
      p ∈ (refineSMatte b1.scale w).matte.disk := by
    rw [← mem_smatte_toRegion, toRegion_refineSMatte]; exact hzw
  refine interpolated_nhds U mm z (mcorner (refineSMatte b1.scale w).matte p + 1)
    (refineSMatte b1.scale w) (refineSRect w.scale b1) (Nat.add_comm _ _)
    (inset_refineSRect w.scale b1 hzb1) ?_ ?_ ⟨p, hp, hpd, Nat.lt_succ_self _⟩
  · rw [toRegion_refineSRect]; exact fun t ht => hrU (hb1r ht)
  · rw [toRegion_refineSMatte]; exact ⟨hzw, hmw, hwU⟩

/-- The part of `U` outside the interpolated region is open. -/
private theorem isOpenRegion_not_smatteInterpolated {U : Region} (hU : IsOpenRegion U)
    (mm : SMatte) : IsOpenRegion (U \ SMatteInterpolated mm.toRegion U) := by
  rintro z ⟨hzU, hz1⟩
  obtain ⟨r, hzr, hrU⟩ := hU z hzU
  obtain ⟨b, hzb, hbr⟩ := approx_rect hzr
  -- No point of `b` is interpolated: otherwise `z` itself would be.
  have hclaim : ∀ t ∈ b.toRegion, t ∉ SMatteInterpolated mm.toRegion U := by
    rintro t htb ⟨w, htw, hmw, hwU⟩
    set B := refineSRect (w.scale + 1) b with hB
    set M := refineSMatte (b.scale + 1) w with hM
    have hscale : B.scale = M.scale := by
      rw [hB, hM]
      change b.scale + (w.scale + 1) = w.scale + (b.scale + 1)
      omega
    have hcoarse : CoarseIn B.rect.toRegion M.matte := by
      have : M.matte = refineMatte (refineMatte^[b.scale] w.matte) := by
        rw [hM]; simp [refineSMatte, Function.iterate_succ_apply']
      rw [this]; exact refineMatte_coarseIn _ _
    obtain ⟨p, hp, hpi⟩ : ∃ p : GPoint, ApproxPoint B.scale z p ∧ p ∈ B.rect.inset.toRegion :=
      inset_refineSRect (w.scale + 1) b hzb
    obtain ⟨q, hq, hqr⟩ : ∃ q : GPoint, ApproxPoint B.scale t q ∧ q ∈ B.rect.toRegion := by
      rw [← mem_srect_toRegion, hB, toRegion_refineSRect]; exact htb
    obtain ⟨q', hq', hq'd⟩ : ∃ q' : GPoint, ApproxPoint M.scale t q' ∧ q' ∈ M.matte.disk := by
      rw [← mem_smatte_toRegion, hM, toRegion_refineSMatte]; exact htw
    have hqq : q' = q := approxPoint_inj (by rw [hscale]; exact hq') hq
    obtain ⟨xm, hext, hsub, hxp⟩ :=
      coarse_extends_in hcoarse ⟨q, hqq ▸ hq'd, hqr⟩ hpi
    refine hz1 ⟨⟨B.scale, xm⟩, ⟨p, hp, hxp⟩, ?_, ?_⟩
    · intro u hu
      obtain ⟨c, hc1, hc2⟩ : ∃ c : GPoint, ApproxPoint M.scale u c ∧ c ∈ M.matte.disk := by
        rw [← mem_smatte_toRegion, hM, toRegion_refineSMatte]; exact hmw hu
      exact ⟨c, show ApproxPoint B.scale u c by rw [hscale]; exact hc1, hext.subset c hc2⟩
    · rintro u ⟨c, hc1, hc2⟩
      rcases hsub c hc2 with h | h
      · have hub : u ∈ B.toRegion := ⟨c, hc1, h⟩
        rw [hB, toRegion_refineSRect] at hub
        exact hrU (hbr hub)
      · have hum : u ∈ M.toRegion := ⟨c, by rw [← hscale]; exact hc1, h⟩
        rw [hM, toRegion_refineSMatte] at hum
        exact hwU hum
  -- Around `z` the whole of `ltouch p` stays inside `b`.
  obtain ⟨p, hp, hpi⟩ : ∃ p : GPoint, ApproxPoint b.scale z p ∧ p ∈ b.rect.inset.toRegion := hzb
  obtain ⟨rp, hzrp, hrpsub⟩ := rect_approx hp
  refine ⟨rp, hzrp, fun u hu => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hrpsub hu
  have hub : u ∈ b.toRegion :=
    ⟨c, hc1, (GRect.mem_inset_iff _ p).mp hpi (ltouch_subset_gtouch p hc2)⟩
  exact ⟨hrU (hbr hub), hclaim u hub⟩

/-- **The interpolation theorem.**  Inside an open connected region, every point
is reached by a scaled matte that contains a given scaled matte of the region and
stays inside the region. -/
theorem connected_matte {U : Region} (hUopen : IsOpenRegion U)
    (hUconn : IsConnectedRegion U) {mm : SMatte} (hmU : mm.toRegion ⊆ U) :
    U ⊆ SMatteInterpolated mm.toRegion U := by
  classical
  intro z hz
  by_contra hz1
  -- The matte is nonempty, so the interpolated region meets `U`.
  obtain ⟨p0, hp0⟩ := mm.matte.disk_nonempty
  have hz0 : scalePoint mm.scale p0 ∈ mm.toRegion := memApprox_scalePoint.mpr hp0
  have hmeet : (SMatteInterpolated mm.toRegion U ∩ U).Nonempty :=
    ⟨scalePoint mm.scale p0, ⟨mm, hz0, fun _ h => h, hmU⟩, hmU hz0⟩
  have hmeet2 : ((U \ SMatteInterpolated mm.toRegion U) ∩ U).Nonempty := ⟨z, ⟨hz, hz1⟩, hz⟩
  obtain ⟨w, hw1, hw2⟩ :=
    hUconn (SMatteInterpolated mm.toRegion U) (U \ SMatteInterpolated mm.toRegion U)
      (isOpenRegion_smatteInterpolated hUopen mm)
      (isOpenRegion_not_smatteInterpolated hUopen mm)
      (fun t ht => by
        by_cases h : t ∈ SMatteInterpolated mm.toRegion U
        · exact Or.inl h
        · exact Or.inr ⟨ht, h⟩)
      hmeet hmeet2
  exact hw2.2 hw1

/-! ### Step 2: adjacency boxes

For each pair of adjacent regions we pick a non-corner point of their common
border and a rectangle around it that no third region comes near; separating
rectangles make the choices for distinct pairs disjoint.  Approximating these
rectangles by grid rectangles at a common scale gives the adjacency boxes.
-/

/-- The intersection of a finite list of rectangles. -/
noncomputable def capList (r₀ : Rect) (l : List Rect) : Rect := l.foldr Rect.cap r₀

/-- A point lies in the intersection exactly when it lies in every factor. -/
theorem mem_capList {r₀ : Rect} : ∀ (l : List Rect) {z : Point},
    z ∈ (capList r₀ l).toRegion ↔ z ∈ r₀.toRegion ∧ ∀ r ∈ l, z ∈ r.toRegion := by
  intro l
  induction l with
  | nil => intro z; simp [capList]
  | cons a t ih =>
    intro z
    have hstep : capList r₀ (a :: t) = Rect.cap a (capList r₀ t) := rfl
    rw [hstep, Rect.mem_cap, ih]
    constructor
    · rintro ⟨ha, h0, hall⟩
      refine ⟨h0, fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ha
      · exact hall r hr
    · rintro ⟨h0, hall⟩
      exact ⟨hall a (by simp), h0, fun r hr => hall r (by simp [hr])⟩

/-- The empty grid rectangle, used to record the absence of an adjacency. -/
def emptyGRect : GRect := ⟨0, 0, 0, 0⟩

/-- The empty rectangle contains no pixel. -/
theorem notMem_emptyGRect (p : GPoint) : p ∉ emptyGRect.toRegion := by
  simp only [emptyGRect, GRect.mem_toRegion]
  omega

/-- The empty rectangle is improper. -/
theorem not_proper_emptyGRect : ¬ emptyGRect.Proper := by
  simp [emptyGRect, GRect.Proper, GRect.area, GRect.width, GRect.height, zwidth]

/-- Membership in an iterated refinement. -/
theorem mem_iterate_refineRect : ∀ (n : ℕ) (r : GRect) (p : GPoint),
    p ∈ (refineRect^[n] r).toRegion ↔ halfg^[n] p ∈ r.toRegion := by
  intro n
  induction n with
  | zero => intro r p; simp
  | succ n ih =>
    intro r p
    rw [Function.iterate_succ_apply' refineRect n r, mem_refineRect, ih,
      Function.iterate_succ_apply]

/-- Properness is preserved by iterated refinement. -/
theorem proper_iterate_refineRect : ∀ (n : ℕ) (r : GRect),
    (refineRect^[n] r).Proper ↔ r.Proper := by
  intro n
  induction n with
  | zero => intro r; simp
  | succ n ih => intro r; rw [Function.iterate_succ_apply, ih, proper_refineRect]

/-- Two points of the same region of a plain map have the same transversal
index. -/
theorem eq_of_mem_same (hm : PlainMap m₀) {Nr : ℕ} {mr : Fin Nr → Point}
    (hmr : MrProper m₀ mr) {w : Point} {i j : Fin Nr}
    (hi : mr i ∈ m₀ w) (hj : mr j ∈ m₀ w) : i = j :=
  (hmr i).2 j (hm.trans _ _ (hm.symm _ _ hi) hj)

/-- A non-corner point cannot lie in the closure of three distinct regions. -/
theorem not_three_closures (hm : PlainMap m₀) {Nr : ℕ} {mr : Fin Nr → Point}
    (hmr : MrProper m₀ mr) {z : Point} (hz : z ∈ notCorner m₀)
    {i j l : Fin Nr} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : z ∈ regionClosure (m₀ (mr i))) (hj : z ∈ regionClosure (m₀ (mr j)))
    (hl : z ∈ regionClosure (m₀ (mr l))) : False := by
  obtain ⟨f, hf⟩ := hz
  have key : ∀ a : Fin Nr, z ∈ regionClosure (m₀ (mr a)) → ∃ k < 2, mr a ∈ m₀ (f k) := by
    intro a ha
    obtain ⟨k, hk2, hk⟩ := hf (mr a) ⟨(hmr a).1, ha⟩
    exact ⟨k, hk2, hk.1⟩
  obtain ⟨ki, hki2, hki⟩ := key i hi
  obtain ⟨kj, hkj2, hkj⟩ := key j hj
  obtain ⟨kl, hkl2, hkl⟩ := key l hl
  have hcase : ki = kj ∨ ki = kl ∨ kj = kl := by omega
  rcases hcase with h | h | h
  · exact hij (eq_of_mem_same hm hmr hki (h ▸ hkj))
  · exact hil (eq_of_mem_same hm hmr hki (h ▸ hkl))
  · exact hjl (eq_of_mem_same hm hmr hkj (h ▸ hkl))

/-- An adjacency index is determined by the pair of regions it names. -/
theorem adjIndex_eq_of_incident {Nr : ℕ} {e f : AdjIndex Nr}
    (h1 : e.Incident f.fst) (h2 : e.Incident f.snd) : e = f := by
  have hf := f.lt
  have he := e.lt
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1 ▸ h2 ▸ hf) (lt_irrefl _)
  · exact AdjIndex.ext' h1.symm h2.symm
  · exact absurd (lt_trans (h1 ▸ hf) (h2 ▸ he)) (lt_irrefl _)
  · exact absurd (h1 ▸ h2 ▸ hf) (lt_irrefl _)

/-- A scaled rectangle properly witnesses the adjacency `e`: each of the two
named regions reaches its inset, and no other region meets it at all. -/
def ABMrProper (m₀ : PlaneMap) {Nr : ℕ} (mr : Fin Nr → Point) (b : SRect)
    (e : AdjIndex Nr) (i : Fin Nr) : Prop :=
  b.rect.Proper →
    (e.Incident i → (b.inset.toRegion ∩ m₀ (mr i)).Nonempty) ∧
      ((b.toRegion ∩ m₀ (mr i)).Nonempty → e.Incident i)

/-- The adjacency indices realised by genuinely adjacent regions. -/
def MrAdj (m₀ : PlaneMap) {Nr : ℕ} (mr : Fin Nr → Point) (e : AdjIndex Nr) : Prop :=
  Adjacent m₀ (mr e.fst) (mr e.snd)

/-- **The adjacency boxes.**  There are pairwise disjoint grid rectangles, all
read at one common scale, that properly witness every adjacency of the
transversal. -/
theorem exists_adjbox (hm : SimpleMap m₀) {Nr : ℕ} {mr : Fin Nr → Point}
    (hmr : MrProper m₀ mr) :
    ∃ (s : ℕ) (ab : AdjBox Nr), ABProper ab ∧
      (∀ (e : AdjIndex Nr) (i : Fin Nr), ABMrProper m₀ mr ⟨s, ab e⟩ e i) ∧
      (∀ e : AdjIndex Nr, MrAdj m₀ mr e → (ab e).Proper) := by
  classical
  -- A non-corner border point for each genuine adjacency.
  have hap0 : ∀ e : AdjIndex Nr, ∃ z : Point,
      MrAdj m₀ mr e → z ∈ notCorner m₀ ∩ border m₀ (mr e.fst) (mr e.snd) := by
    intro e
    by_cases h : MrAdj m₀ mr e
    · obtain ⟨z, hz⟩ := h.2
      exact ⟨z, fun _ => hz⟩
    · exact ⟨(0, 0), fun hc => absurd hc h⟩
  choose ap hap using hap0
  -- A rectangle around it that only the two named regions come near.
  have harr0 : ∀ (e : AdjIndex Nr) (i : Fin Nr), ∃ r : Rect, ap e ∈ r.toRegion ∧
      (MrAdj m₀ mr e → (r.toRegion ∩ regionClosure (m₀ (mr i))).Nonempty → e.Incident i) := by
    intro e i
    by_cases harc : MrAdj m₀ mr e
    · by_cases hinc : e.Incident i
      · exact ⟨sepRect (ap e) (ap e), mem_sepRect _ _, fun _ _ => hinc⟩
      · by_cases hex : ∃ r : Rect, ap e ∈ r.toRegion ∧
            ((r.toRegion ∩ regionClosure (m₀ (mr i))).Nonempty → e.Incident i)
        · obtain ⟨r, h1, h2⟩ := hex
          exact ⟨r, h1, fun _ => h2⟩
        · exfalso
          have hcl : ap e ∈ regionClosure (m₀ (mr i)) := by
            intro U hUopen hapU
            by_contra hnon
            obtain ⟨r, hzr, hrU⟩ := hUopen (ap e) hapU
            refine hex ⟨r, hzr, fun hmeet => ?_⟩
            obtain ⟨v, hvr, hvcl⟩ := hmeet
            exact absurd (hvcl U hUopen (hrU hvr)) hnon
          have habe := hap e harc
          rw [AdjIndex.Incident, not_or] at hinc
          exact not_three_closures hm.plain hmr habe.1 hinc.1 hinc.2 e.fst_ne_snd hcl
            habe.2.1 habe.2.2
    · exact ⟨sepRect (ap e) (ap e), mem_sepRect _ _, fun hc => absurd hc harc⟩
  choose arr harr1 harr2 using harr0
  -- Intersect over all regions, then separate the different adjacencies.
  set ar0 : AdjIndex Nr → Rect := fun e =>
    capList (sepRect (ap e) (ap e)) ((Finset.univ : Finset (Fin Nr)).toList.map (arr e))
    with har0
  set ar : AdjIndex Nr → Rect := fun e => capList (ar0 e)
    ((Finset.univ : Finset (AdjIndex Nr)).toList.map fun f => sepRect (ap f) (ap e)) with har
  have hape : ∀ e, ap e ∈ (ar e).toRegion := by
    intro e
    refine mem_capList _ |>.mpr ⟨mem_capList _ |>.mpr ⟨mem_sepRect _ _, ?_⟩, ?_⟩
    · intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      exact harr1 e i
    · intro r hr
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hr
      exact mem_sepRect _ _
  have harsub : ∀ (e : AdjIndex Nr) (i : Fin Nr), (ar e).toRegion ⊆ (arr e i).toRegion := by
    intro e i v hv
    exact (mem_capList _ |>.mp ((mem_capList _ |>.mp hv).1)).2 _
      (List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ i)))
  have harsep : ∀ e f : AdjIndex Nr,
      (ar e).toRegion ⊆ (sepRect (ap f) (ap e)).toRegion := by
    intro e f v hv
    exact (mem_capList _ |>.mp hv).2 _
      (List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ f)))
  have harinj : ∀ e f : AdjIndex Nr, MrAdj m₀ mr e → MrAdj m₀ mr f →
      ((ar e).toRegion ∩ (ar f).toRegion).Nonempty → e = f := by
    rintro e f he hf ⟨v, hve, hvf⟩
    have hpeq : ap f = ap e := meet_sepRect ⟨v, harsep e f hve, harsep f e hvf⟩
    have h1 : e.Incident f.fst :=
      harr2 e f.fst he ⟨ap e, harsub e f.fst (hape e), hpeq ▸ (hap f hf).2.1⟩
    have h2 : e.Incident f.snd :=
      harr2 e f.snd he ⟨ap e, harsub e f.snd (hape e), hpeq ▸ (hap f hf).2.2⟩
    exact adjIndex_eq_of_incident h1 h2
  -- Approximate each rectangle by a grid rectangle, then unify the scales.
  choose b0 hb0i hb0r using fun e : AdjIndex Nr => approx_rect (hape e)
  set S := (∑ e : AdjIndex Nr, (b0 e).scale) + 1 with hSdef
  have hle : ∀ e : AdjIndex Nr, (b0 e).scale + 1 ≤ S := by
    intro e
    have h := Finset.single_le_sum (f := fun e : AdjIndex Nr => (b0 e).scale)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    omega
  set u : AdjIndex Nr → ℕ := fun e => S - 1 - (b0 e).scale with hudef
  have hSu : ∀ e : AdjIndex Nr, (refineSRect (u e + 1) (b0 e)).scale = S := by
    intro e
    have h := hle e
    simp only [refineSRect, hudef]
    omega
  set ab : AdjBox Nr := fun e =>
    if MrAdj m₀ mr e then (refineSRect (u e + 1) (b0 e)).rect else emptyGRect with habdef
  have habe : ∀ e : AdjIndex Nr, MrAdj m₀ mr e →
      (⟨S, ab e⟩ : SRect) = refineSRect (u e + 1) (b0 e) := by
    intro e he
    have h1 : ab e = (refineSRect (u e + 1) (b0 e)).rect := by
      simp [habdef, he]
    rw [h1, ← hSu e]
  have harc_of : ∀ e : AdjIndex Nr, (ab e).Proper → MrAdj m₀ mr e := by
    intro e hp
    by_contra h
    have h1 : ab e = emptyGRect := by simp [habdef, h]
    rw [h1] at hp
    exact not_proper_emptyGRect hp
  have hb0proper : ∀ e : AdjIndex Nr, (b0 e).rect.Proper := by
    intro e
    obtain ⟨p, _, hpi⟩ := hb0i e
    exact (GRect.proper_iff_nonempty _).mpr ⟨p, GRect.mem_of_mem_inset hpi⟩
  have habproper : ∀ e : AdjIndex Nr, MrAdj m₀ mr e → (ab e).Proper := by
    intro e he
    have h1 : ab e = (refineSRect (u e + 1) (b0 e)).rect := by
      simp [habdef, he]
    rw [h1]
    exact (proper_iterate_refineRect _ _).mpr (hb0proper e)
  -- The scaled box of `e` denotes exactly the rectangle `ar e` approximates.
  have habregion : ∀ e : AdjIndex Nr, MrAdj m₀ mr e →
      (⟨S, ab e⟩ : SRect).toRegion ⊆ (ar e).toRegion := by
    intro e he
    rw [habe e he, toRegion_refineSRect]
    exact hb0r e
  refine ⟨S, ab, ?_, ?_, habproper⟩
  · -- Disjointness.
    intro e f p hpe hpf
    have hae : MrAdj m₀ mr e := by
      by_contra h
      have h1 : ab e = emptyGRect := by simp [habdef, h]
      rw [h1] at hpe
      exact notMem_emptyGRect p hpe
    have haf : MrAdj m₀ mr f := by
      by_contra h
      have h1 : ab f = emptyGRect := by simp [habdef, h]
      rw [h1] at hpf
      exact notMem_emptyGRect p hpf
    refine harinj e f hae haf ⟨scalePoint S p, habregion e hae ?_, habregion f haf ?_⟩
    · exact memApprox_scalePoint.mpr hpe
    · exact memApprox_scalePoint.mpr hpf
  · -- Properness of the witness.
    intro e i hprop
    have hae : MrAdj m₀ mr e := harc_of e hprop
    constructor
    · intro hinc
      have hcl : ap e ∈ regionClosure (m₀ (mr i)) := by
        rcases hinc with rfl | rfl
        · exact (hap e hae).2.1
        · exact (hap e hae).2.2
      -- Refine once, so that the whole of `ltouch p` stays inset.
      have h2 : ap e ∈ memApprox ((b0 e).scale + 1)
          (refineRect ((b0 e).rect.inset)).toRegion := by
        rw [toRegion_refineRect, memApprox_refine]
        exact hb0i e
      obtain ⟨p, hp, hpr⟩ := h2
      rw [refine_inset] at hpr
      obtain ⟨r, hzr, hrsub⟩ := rect_approx hp
      obtain ⟨v, hvm, hvr⟩ := hcl r.toRegion (isOpenRegion_rect r) hzr
      obtain ⟨c, hc, hcl'⟩ := hrsub hvr
      have hcin : c ∈ ((refineRect (b0 e).rect).inset).toRegion :=
        (GRect.mem_inset_iff _ p).mp hpr (ltouch_subset_gtouch p hcl')
      have hv1 : v ∈ (refineSRect 1 (b0 e)).inset.toRegion := by
        refine ⟨c, hc, ?_⟩
        simpa only [refineSRect, Function.iterate_one, SRect.inset] using hcin
      have hv2 : v ∈ (refineSRect (u e) (refineSRect 1 (b0 e))).inset.toRegion :=
        inset_refineSRect (u e) _ hv1
      rw [← refineSRect_add] at hv2
      rw [habe e hae]
      exact ⟨v, hv2, hvm⟩
    · rintro ⟨v, hvb, hvm⟩
      exact harr2 e i hae
        ⟨v, harsub e i (habregion e hae hvb), subset_regionClosure _ hvm⟩

/-! ### Step 4: matte approximations of the regions

Each region is approximated from inside by a scaled matte that reaches the inset
of every adjacency box incident to it; the interpolation theorem grows the matte
one box at a time.
-/

/-- A single-pixel scaled matte inside a given region of an open map. -/
private theorem exists_base_smatte {U : Region} (hU : IsOpenRegion U) {z : Point}
    (hz : z ∈ U) : ∃ w : SMatte, w.toRegion ⊆ U := by
  obtain ⟨r, hzr, hrsub⟩ := hU z hz
  obtain ⟨b, hbi, hbr⟩ := approx_rect hzr
  obtain ⟨p, _, hpi⟩ := hbi
  refine ⟨⟨b.scale, pointMatte p⟩, ?_⟩
  rintro t ⟨q, hq, hqd⟩
  have hqp : q = p := Finset.mem_singleton.mp hqd
  exact hrsub (hbr ⟨q, hq, hqp ▸ GRect.mem_of_mem_inset hpi⟩)

/-- **The region mattes.**  At one common scale there are mattes, one per
region, each contained in its region and meeting the inset of every adjacency
box incident to it. -/
theorem exists_smatte (hm : SimpleMap m₀) {Nr : ℕ} {mr : Fin Nr → Point}
    (hmr : MrProper m₀ mr) {s : ℕ} {ab : AdjBox Nr}
    (habP : ∀ (e : AdjIndex Nr) (i : Fin Nr), ABMrProper m₀ mr ⟨s, ab e⟩ e i) :
    ∃ (t : ℕ) (cm : Fin Nr → Matte), ∀ i : Fin Nr,
      (⟨t, cm i⟩ : SMatte).toRegion ⊆ m₀ (mr i) ∧
        ∀ e : AdjIndex Nr, e.Incident i → (ab e).Proper →
          ((⟨t, cm i⟩ : SMatte).toRegion ∩ (⟨s, ab e⟩ : SRect).inset.toRegion).Nonempty := by
  classical
  have hstep : ∀ (i : Fin Nr) (E : List (AdjIndex Nr)), ∃ w : SMatte,
      w.toRegion ⊆ m₀ (mr i) ∧ ∀ e ∈ E, e.Incident i → (ab e).Proper →
        (w.toRegion ∩ (⟨s, ab e⟩ : SRect).inset.toRegion).Nonempty := by
    intro i E
    induction E with
    | nil =>
      obtain ⟨w, hw⟩ := exists_base_smatte (hm.isOpen (mr i)) (hmr i).1
      exact ⟨w, hw, by simp⟩
    | cons e E ih =>
      obtain ⟨w, hwsub, hwE⟩ := ih
      by_cases hinc : e.Incident i
      · by_cases hprop : (ab e).Proper
        · obtain ⟨z, hz1, hz2⟩ := ((habP e i hprop).1 hinc)
          obtain ⟨w1, hw1z, hw1m, hw1U⟩ :=
            connected_matte (hm.isOpen (mr i)) (hm.isConnected (mr i)) hwsub hz2
          refine ⟨w1, hw1U, fun f hf hfi hfp => ?_⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · exact ⟨z, hw1z, hz1⟩
          · obtain ⟨v, hv1, hv2⟩ := hwE f hf hfi hfp
            exact ⟨v, hw1m hv1, hv2⟩
        · refine ⟨w, hwsub, fun f hf hfi hfp => ?_⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · exact absurd hfp hprop
          · exact hwE f hf hfi hfp
      · refine ⟨w, hwsub, fun f hf hfi hfp => ?_⟩
        rcases List.mem_cons.mp hf with rfl | hf
        · exact absurd hfi hinc
        · exact hwE f hf hfi hfp
  choose w hwsub hwmeet using
    fun i : Fin Nr => hstep i (Finset.univ : Finset (AdjIndex Nr)).toList
  -- Refine all the mattes to a common scale.
  set T := ∑ i : Fin Nr, (w i).scale with hTdef
  have hle : ∀ i : Fin Nr, (w i).scale ≤ T :=
    fun i => Finset.single_le_sum (f := fun i : Fin Nr => (w i).scale)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set v : Fin Nr → ℕ := fun i => T - (w i).scale with hvdef
  have hTv : ∀ i : Fin Nr, (refineSMatte (v i) (w i)).scale = T := by
    intro i
    have h := hle i
    simp only [refineSMatte, hvdef]
    omega
  have hcm : ∀ i : Fin Nr, (⟨T, (refineSMatte (v i) (w i)).matte⟩ : SMatte)
      = refineSMatte (v i) (w i) := by
    intro i
    rw [← hTv i]
  refine ⟨T, fun i => (refineSMatte (v i) (w i)).matte, fun i => ?_⟩
  rw [hcm i, toRegion_refineSMatte]
  exact ⟨hwsub i, fun e hei hep =>
    hwmeet i e (Finset.mem_toList.mpr (Finset.mem_univ e)) hei hep⟩

/-! ### Step 5: the discretisation theorem -/

/-- Adjacency is symmetric. -/
theorem Adjacent.symm' (hm : PlainMap m₀) {z t : Point} (h : Adjacent m₀ z t) :
    Adjacent m₀ t z := by
  refine ⟨fun hc => h.1 (hm.symm _ _ hc), ?_⟩
  obtain ⟨u, hu1, hu2⟩ := h.2
  exact ⟨u, hu1, hu2.2, hu2.1⟩

/-- The four colours enumerated by a natural number. -/
def colorOfNat : ℕ → Color
  | 0 => Color.c0
  | 1 => Color.c1
  | 2 => Color.c2
  | _ => Color.c3

/-- The index of a colour. -/
def natOfColor : Color → ℕ
  | Color.c0 => 0
  | Color.c1 => 1
  | Color.c2 => 2
  | Color.c3 => 3

/-- The enumeration and the indexing of colours are inverse. -/
theorem colorOfNat_natOfColor (c : Color) : colorOfNat (natOfColor c) = c := by
  cases c <;> rfl

/-- There are four colours. -/
theorem natOfColor_lt (c : Color) : natOfColor c < 4 := by cases c <;> decide

/-- **The discretisation theorem.**  Every finite simple map of the real plane
is approximated by a finite planar bridgeless hypermap whose four-colourings
yield four-colourings of the map.  This is the hypothesis `discretize` of
`fourColorTheorem_of`. -/
theorem discretize (m : PlaneMap) (hm : FiniteSimpleMap m) :
    ∃ (E : Type) (_ : Finite E) (G : Hypermap E),
      G.PlanarBridgeless ∧ (G.FourColorable → ColorableWith 4 m) := by
  classical
  obtain ⟨Nr, mr, hmr, hmrcov⟩ := exists_map_repr hm.simple.plain hm.finite
  obtain ⟨s, ab, habP, habmr, habadj⟩ := exists_adjbox hm.simple hmr
  obtain ⟨t, cm, hcmP⟩ := exists_smatte hm.simple hmr habmr
  -- Bring boxes and mattes to a common scale.
  set SS := s + t with hSS
  set abG : AdjBox Nr := fun e => refineRect^[t] (ab e) with habG
  set cmG : CMatte Nr := fun i => refineMatte^[s] (cm i) with hcmG
  have habSR : ∀ e : AdjIndex Nr, (⟨SS, abG e⟩ : SRect) = refineSRect t ⟨s, ab e⟩ := fun _ => rfl
  have hcmSM : ∀ i : Fin Nr, (⟨SS, cmG i⟩ : SMatte) = refineSMatte s ⟨t, cm i⟩ := by
    intro i
    simp only [hSS, hcmG, refineSMatte, SMatte.mk.injEq]
    exact ⟨Nat.add_comm s t, trivial⟩
  have habproper : ∀ e : AdjIndex Nr, (abG e).Proper ↔ (ab e).Proper := by
    intro e; rw [habG]; exact proper_iterate_refineRect t (ab e)
  -- The three well-formedness conditions of the grid map package.
  have hABP : ABProper abG := by
    intro e f p hpe hpf
    rw [habG] at hpe hpf
    exact habP e f (halfg^[t] p) ((mem_iterate_refineRect t (ab e) p).mp hpe)
      ((mem_iterate_refineRect t (ab f) p).mp hpf)
  have hcmsub : ∀ i : Fin Nr, (⟨SS, cmG i⟩ : SMatte).toRegion ⊆ m (mr i) := by
    intro i
    rw [hcmSM i, toRegion_refineSMatte]
    exact (hcmP i).1
  have hCMP : CMProper cmG := by
    rintro i j ⟨p, hpi, hpj⟩
    have hzi : scalePoint SS p ∈ m (mr i) := hcmsub i (memApprox_scalePoint.mpr hpi)
    have hzj : scalePoint SS p ∈ m (mr j) := hcmsub j (memApprox_scalePoint.mpr hpj)
    exact eq_of_mem_same hm.simple.plain hmr (hm.simple.plain.symm _ _ hzi)
      (hm.simple.plain.symm _ _ hzj)
  have habmr2 : ∀ (e : AdjIndex Nr) (i : Fin Nr), ABMrProper m mr ⟨SS, abG e⟩ e i := by
    intro e i hprop
    have hp0 : (ab e).Proper := (habproper e).mp hprop
    refine ⟨fun hinc => ?_, fun hmeet => ?_⟩
    · obtain ⟨z, hz1, hz2⟩ := (habmr e i hp0).1 hinc
      exact ⟨z, by rw [habSR e]; exact inset_refineSRect t _ hz1, hz2⟩
    · refine (habmr e i hp0).2 ?_
      obtain ⟨z, hz1, hz2⟩ := hmeet
      rw [habSR e, toRegion_refineSRect] at hz1
      exact ⟨z, hz1, hz2⟩
  have hABCM : ∀ (e : AdjIndex Nr) (i : Fin Nr), ABCMProper abG cmG e i := by
    intro e i hprop
    have hp0 : (ab e).Proper := (habproper e).mp hprop
    refine ⟨fun hinc => ?_, fun hmeet => ?_⟩
    · obtain ⟨z, hz1, hz2⟩ := (hcmP i).2 e hinc hp0
      obtain ⟨p, hp, hpd⟩ := (by rw [hcmSM i, toRegion_refineSMatte]; exact hz1 :
        z ∈ (⟨SS, cmG i⟩ : SMatte).toRegion)
      obtain ⟨q, hq, hqi⟩ := (by rw [habSR e]; exact inset_refineSRect t _ hz2 :
        z ∈ (⟨SS, abG e⟩ : SRect).inset.toRegion)
      exact ⟨p, hpd, (approxPoint_inj hq hp) ▸ hqi⟩
    · obtain ⟨p, hpd, hpr⟩ := hmeet
      refine (habmr2 e i hprop).2 ⟨scalePoint SS p, memApprox_scalePoint.mpr hpr, ?_⟩
      exact hcmsub i (memApprox_scalePoint.mpr hpd)
  obtain ⟨D, hD, G, hplanar, hbridge, hcolor⟩ := exists_grid_map hABP hCMP hABCM
  refine ⟨D, hD, G, ⟨hplanar, hbridge⟩, fun hfc => ?_⟩
  obtain ⟨k0, hk0⟩ := hcolor hfc
  -- Transport the colouring back to the plane.
  have hkey : ∀ i j : Fin Nr, Adjacent m (mr i) (mr j) → i ≠ j → k0 i ≠ k0 j := by
    intro i j hadj hne
    have hpr : ∀ e : AdjIndex Nr, MrAdj m mr e → (abG e).Proper :=
      fun e he => (habproper e).mpr (habadj e he)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hk0 ⟨i, j, h⟩ (hpr ⟨i, j, h⟩ hadj)
    · exact (hk0 ⟨j, i, h⟩ (hpr ⟨j, i, h⟩ (Adjacent.symm' hm.simple.plain hadj))).symm
  set kk : PlaneMap :=
    fun z => {u | ∃ i : Fin Nr, z ∈ m (mr i) ∧ ∃ j : Fin Nr, u ∈ m (mr j) ∧ k0 i = k0 j}
    with hkkdef
  have hmemkk : ∀ z u : Point, u ∈ kk z ↔
      ∃ i : Fin Nr, z ∈ m (mr i) ∧ ∃ j : Fin Nr, u ∈ m (mr j) ∧ k0 i = k0 j :=
    fun _ _ => Iff.rfl
  have hplain : PlainMap kk := by
    constructor
    · rintro z u ⟨i, hzi, j, huj, hij⟩
      exact ⟨j, huj, i, hzi, hij.symm⟩
    · rintro z u ⟨i, hzi, j, huj, hij⟩ y ⟨a, hua, b, hyb, hab⟩
      have hja : j = a := eq_of_mem_same hm.simple.plain hmr
        (hm.simple.plain.symm _ _ huj) (hm.simple.plain.symm _ _ hua)
      exact ⟨i, hzi, b, hyb, by rw [hij, hja, hab]⟩
  refine ⟨kk, ⟨hplain, ?_, ?_, ?_⟩, ?_⟩
  · rintro z ⟨i, hzi, -⟩
    exact hm.simple.plain.mem_cover_right hzi
  · rintro z u hzu
    obtain ⟨i, hzi⟩ := hmrcov z (hm.simple.plain.mem_cover_left hzu)
    exact ⟨i, hzi, i, hm.simple.plain.trans _ _ hzi hzu, rfl⟩
  · rintro z u hadj ⟨i, hzi, j, huj, hij⟩
    have hne : i ≠ j := by
      rintro rfl
      exact hadj.1 (hm.simple.plain.trans _ _ (hm.simple.plain.symm _ _ hzi) huj)
    refine hkey i j ⟨fun hc => hne ((hmr i).2 j hc), ?_⟩ hne hij
    obtain ⟨y, hy1, hy2⟩ := hadj.2
    refine ⟨y, hy1, ?_, ?_⟩
    · have h := hy2.1
      rwa [hm.simple.plain.region_eq hzi] at h
    · have h := hy2.2
      rwa [hm.simple.plain.region_eq huj] at h
  · have hpick : ∀ c : Color, ∃ p : Point, (∃ i : Fin Nr, k0 i = c) →
        ∃ a : Fin Nr, p = mr a ∧ k0 a = c := by
      intro c
      by_cases h : ∃ i : Fin Nr, k0 i = c
      · obtain ⟨i, hi⟩ := h
        exact ⟨mr i, fun _ => ⟨i, rfl, hi⟩⟩
      · exact ⟨(0, 0), fun hc => absurd hc h⟩
    choose pick hpick using hpick
    refine ⟨fun n => pick (colorOfNat n), fun z hz => ?_⟩
    obtain ⟨i, hzi, -⟩ := hz
    obtain ⟨a, hpa, hka⟩ := hpick (colorOfNat (natOfColor (k0 i)))
      ⟨i, by rw [colorOfNat_natOfColor]⟩
    refine ⟨natOfColor (k0 i), natOfColor_lt _, ?_⟩
    simp only [hpa]
    rw [colorOfNat_natOfColor] at hka
    exact ⟨a, (hmr a).1, i, hzi, hka⟩

-- A sanity check that `discretize` has exactly the shape required by the
-- `discretize` hypothesis of `fourColorTheorem_of` in `FourColor/Combinatorial.lean`.
example : ∀ m : PlaneMap, FiniteSimpleMap m →
    ∃ (E : Type) (_ : Finite E) (G : Hypermap E),
      G.PlanarBridgeless ∧ (G.FourColorable → ColorableWith 4 m) := discretize

end FourColor

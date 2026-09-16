import FourColor.Approx
import Mathlib.Basic.Denumerable
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# From finite maps to arbitrary maps

A compactness argument reducing the Four Colour Theorem for an arbitrary simple
map of the plane to the theorem for *finite* simple maps.

The plane is covered by countably many scaled grid points `stdPoint i`, and
every region of a simple map contains one of them, since regions are open.  The
map `pmap m n` is the restriction of `m` to the regions met by one of the first
`n` grid points; it is a *finite* simple map, so it is colourable by hypothesis,
and a colouring of it separates any two regions of `m` that are adjacent and met
by those grid points.  A limit colour is then chosen for each grid point by an
ultrafilter refining `Filter.atTop`, which makes every finite (indeed, every
pairwise) constraint hold simultaneously; colouring a point by the limit colour
of a grid point in its region gives a colouring of the whole map.

## Main definitions

* `stdPoint` — a surjective enumeration of the scaled grid points
  `scalePoint s p`, the reference's `std_point`.
* `inPmap m n` — the union of the regions of `m` containing one of the first `n`
  scaled grid points.
* `pmap m n` — the restriction of `m` to `inPmap m n`.

## Main results

* `exists_stdPoint_mem` — every region of a simple map contains a grid point
  (the reference's `has_std_point`).
* `pmap_apply` — on `inPmap m n` the partial map `pmap m n` has the very same
  regions as `m`; this is what makes the transfer lemmas below routine.
* `pmap_finiteSimpleMap` — `pmap m n` is a finite simple map.
* `adjacent_pmap` — regions of `m` that are adjacent and met by the first `n`
  grid points are adjacent in `pmap m n`.
* `compactness_extension` — if every finite simple map is `nc`-colourable then
  so is every simple map.
* `fourColorTheorem_of_finite` — `FourColorTheoremFinite → FourColorTheorem`.

## Implementation notes

The reference is at pains to avoid the axiom of choice: it builds the limit
colouring as the union of a chain of *lexicographically minimal* prefix
colourings, which costs it `prefix_coloring`, `minimal`, `extensible`,
`limit_coloring` and some 250 lines of bookkeeping.  Here Mathlib's classical
choice is available, so the limit is obtained directly from an ultrafilter
refining `Filter.atTop`, and none of that machinery is needed.  The reference's
`at_most_regionsP`, which it flags as "not used in the current proof", is
skipped as well.

## References

Gonthier's `theories/proof/finitize.v`.
-/

namespace FourColor

variable {m : PlaneMap} {z z₁ z₂ t : Point}

/-! ### Plain map generalities -/

/-- Membership in the covered region is membership in one's own region. -/
theorem mem_cover_iff : z ∈ cover m ↔ z ∈ m z := Iff.rfl

/-- Two related points have the very same region. -/
theorem PlainMap.region_eq (hm : PlainMap m) (h : z₂ ∈ m z₁) : m z₂ = m z₁ :=
  Set.Subset.antisymm (hm.trans _ _ h) (hm.trans _ _ (hm.symm _ _ h))

/-- The source of a relation is covered. -/
theorem PlainMap.mem_cover_left (hm : PlainMap m) (h : z₂ ∈ m z₁) : z₁ ∈ cover m :=
  hm.trans _ _ h (hm.symm _ _ h)

/-- The target of a relation is covered. -/
theorem PlainMap.mem_cover_right (hm : PlainMap m) (h : z₂ ∈ m z₁) : z₂ ∈ cover m := by
  rw [mem_cover_iff, hm.region_eq h]
  exact h

/-- Adjacency only depends on the two regions involved. -/
theorem Adjacent.congr (hm : PlainMap m) {w₁ w₂ : Point} (h : Adjacent m z₁ z₂)
    (h₁ : w₁ ∈ m z₁) (h₂ : w₂ ∈ m z₂) : Adjacent m w₁ w₂ := by
  have e₁ : m w₁ = m z₁ := hm.region_eq h₁
  have e₂ : m w₂ = m z₂ := hm.region_eq h₂
  refine ⟨?_, ?_⟩
  · rw [e₁]
    intro hw
    have hz : m z₂ = m z₁ := by rw [← e₂]; exact hm.region_eq hw
    exact h.1 (hz ▸ hm.mem_cover_left h₂)
  · simpa only [border, e₁, e₂] using h.2

/-! ### The empty region -/

/-- The empty region is open. -/
theorem isOpenRegion_empty : IsOpenRegion (∅ : Region) := by
  intro z hz
  simp only [Set.mem_empty_iff_false] at hz

/-- The empty region is connected. -/
theorem isConnectedRegion_empty : IsConnectedRegion (∅ : Region) := by
  intro u v _ _ _ hu _
  obtain ⟨w, -, hw⟩ := hu
  simp only [Set.mem_empty_iff_false] at hw

/-! ### A canonical enumeration of the scaled grid points -/

/-- The `i`-th scaled grid point, in a fixed enumeration of scales and grid
points.  This is the reference's `std_point`. -/
noncomputable def stdPoint (i : ℕ) : Point :=
  scalePoint (Denumerable.ofNat (ℕ × GPoint) i).1 (Denumerable.ofNat (ℕ × GPoint) i).2

/-- Every scaled grid point occurs in the enumeration. -/
theorem exists_stdPoint (s : ℕ) (p : GPoint) : ∃ i, stdPoint i = scalePoint s p :=
  ⟨Encodable.encode (s, p), by simp only [stdPoint, Denumerable.ofNat_encode]⟩

/-- Every open rectangle that contains a point contains a scaled grid point. -/
theorem exists_stdPoint_mem_rect {r : Rect} (hz : z ∈ r.toRegion) :
    ∃ i, stdPoint i ∈ r.toRegion := by
  obtain ⟨b, hzb, hbr⟩ := approx_rect hz
  obtain ⟨p, -, hpb⟩ := hzb
  obtain ⟨i, hi⟩ := exists_stdPoint b.scale p
  refine ⟨i, hbr ?_⟩
  rw [hi]
  refine memApprox_scalePoint.mpr ?_
  simp only [SRect.inset, GRect.inset, GRect.mem_toRegion] at hpb ⊢
  omega

/-- Every region of a simple map contains a scaled grid point: the reference's
`has_std_point`. -/
theorem exists_stdPoint_mem (hm : SimpleMap m) (hz : z ∈ cover m) :
    ∃ i, stdPoint i ∈ m z := by
  obtain ⟨u, hzu, hur⟩ := hm.isOpen z z hz
  obtain ⟨i, hi⟩ := exists_stdPoint_mem_rect hzu
  exact ⟨i, hur hi⟩

/-! ### Partial maps -/

/-- The union of the regions of `m` containing one of the first `n` scaled grid
points. -/
def inPmap (m : PlaneMap) (n : ℕ) : Region := {z | ∃ i < n, stdPoint i ∈ m z}

/-- The restriction of the map `m` to `inPmap m n`. -/
def pmap (m : PlaneMap) (n : ℕ) : PlaneMap :=
  fun z₁ => {z₂ | z₁ ∈ inPmap m n ∧ z₂ ∈ inPmap m n ∧ z₂ ∈ m z₁}

/-- `inPmap` is monotone in the number of grid points. -/
theorem inPmap_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : inPmap m n₁ ⊆ inPmap m n₂ :=
  fun _ ⟨i, hi, hmem⟩ => ⟨i, lt_of_lt_of_le hi h, hmem⟩

/-- A point of `inPmap m n` is covered by `m`. -/
theorem mem_cover_of_mem_inPmap (hm : PlainMap m) {n : ℕ} (hz : z ∈ inPmap m n) :
    z ∈ cover m :=
  hm.mem_cover_left hz.choose_spec.2

/-- `inPmap m n` is a union of regions of `m`. -/
theorem mem_inPmap_of_mem_region (hm : PlainMap m) {n : ℕ} (hz : z ∈ inPmap m n)
    (ht : t ∈ m z) : t ∈ inPmap m n := by
  obtain ⟨i, hi, hmem⟩ := hz
  exact ⟨i, hi, by rw [hm.region_eq ht]; exact hmem⟩

/-- On `inPmap m n` the partial map has exactly the regions of `m`. -/
theorem pmap_apply (hm : PlainMap m) {n : ℕ} (hz : z ∈ inPmap m n) : pmap m n z = m z := by
  ext u
  exact ⟨fun h => h.2.2, fun h => ⟨hz, mem_inPmap_of_mem_region hm hz h, h⟩⟩

/-- Off `inPmap m n` the partial map has empty regions. -/
theorem pmap_apply_empty {n : ℕ} (hz : z ∉ inPmap m n) : pmap m n z = ∅ := by
  ext u
  simp only [pmap, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact fun h => hz h.1

/-- The region covered by `pmap m n` is `inPmap m n`. -/
theorem cover_pmap (hm : PlainMap m) (n : ℕ) : cover (pmap m n) = inPmap m n := by
  ext u
  refine ⟨fun h => h.1, fun h => ⟨h, h, ?_⟩⟩
  exact mem_cover_of_mem_inPmap (m := m) hm h

/-- A partial map of a plain map is plain. -/
theorem pmap_plain (hm : PlainMap m) (n : ℕ) : PlainMap (pmap m n) :=
  ⟨fun _ _ h => ⟨h.2.1, h.1, hm.symm _ _ h.2.2⟩,
   fun _ _ h _ hu => ⟨h.1, hu.2.1, hm.trans _ _ h.2.2 hu.2.2⟩⟩

/-- A partial map is included in the map it restricts: the reference's
`pmap_sub`. -/
theorem pmap_submap (n : ℕ) : Submap (pmap m n) m := fun _ _ h => h.2.2

/-- Partial maps grow with the number of grid points: the reference's
`pmap_le`. -/
theorem pmap_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : Submap (pmap m n₁) (pmap m n₂) :=
  fun _ _ hz => ⟨inPmap_mono h hz.1, inPmap_mono h hz.2.1, hz.2.2⟩

/-- `pmap m n` has at most `n` regions: one for each of the first `n` grid
points. -/
theorem pmap_atMostRegions (hm : PlainMap m) (n : ℕ) : AtMostRegions n (pmap m n) := by
  refine ⟨stdPoint, fun z hz => ?_⟩
  obtain ⟨i, hi, hmem⟩ := hz.1
  exact ⟨i, hi, ⟨i, hi, hm.mem_cover_right hmem⟩, hz.2.1, hm.symm _ _ hmem⟩

/-- The partial maps of a simple map are finite simple maps: this is the
reference's `pmap_finite`. -/
theorem pmap_finiteSimpleMap (hm : SimpleMap m) (n : ℕ) : FiniteSimpleMap (pmap m n) := by
  refine ⟨⟨pmap_plain hm.plain n, fun z => ?_, fun z => ?_⟩, n, pmap_atMostRegions hm.plain n⟩
  · by_cases hz : z ∈ inPmap m n
    · rw [pmap_apply hm.plain hz]; exact hm.isOpen z
    · rw [pmap_apply_empty hz]; exact isOpenRegion_empty
  · by_cases hz : z ∈ inPmap m n
    · rw [pmap_apply hm.plain hz]; exact hm.isConnected z
    · rw [pmap_apply_empty hz]; exact isConnectedRegion_empty

/-- Non-corner points of `m` are non-corner points of its partial maps. -/
theorem notCorner_pmap (hm : PlainMap m) {n : ℕ} (hz : z ∈ notCorner m) :
    z ∈ notCorner (pmap m n) := by
  obtain ⟨f, hf⟩ := hz
  refine ⟨f, fun u hu => ?_⟩
  have hun : u ∈ inPmap m n := hu.1.1
  have hum : u ∈ cover m := mem_cover_of_mem_inPmap (m := m) hm hun
  have hclos : z ∈ regionClosure (m u) := by rw [← pmap_apply hm hun]; exact hu.2
  obtain ⟨i, hi, hmem, hcl⟩ := hf u ⟨hum, hclos⟩
  have hfi : f i ∈ inPmap m n := by
    obtain ⟨j, hj, hjm⟩ := hun
    exact ⟨j, hj, by rw [← hm.region_eq hmem]; exact hjm⟩
  refine ⟨i, hi, ?_⟩
  simp only [cornerMap, Set.mem_ofPred_eq, pmap_apply hm hfi]
  exact ⟨hmem, hcl⟩

/-- Adjacent regions of `m` met by the first `n` grid points stay adjacent in
`pmap m n`. -/
theorem adjacent_pmap (hm : PlainMap m) {n : ℕ} (h : Adjacent m z₁ z₂)
    (h₁ : z₁ ∈ inPmap m n) (h₂ : z₂ ∈ inPmap m n) : Adjacent (pmap m n) z₁ z₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := h.2
  refine ⟨fun hc => h.1 hc.2.2, ⟨w, ⟨notCorner_pmap hm hw₁, ?_⟩⟩⟩
  simpa only [border, pmap_apply hm h₁, pmap_apply hm h₂] using hw₂

/-! ### Colourings as colour functions -/

/-- A plain map with at most `nc` regions is the same-colour relation of a
colour function with values below `nc`.  This replaces the reference's
`at_most_regionsP`, which encodes colours as the first `nc` naturals of the
real line. -/
theorem exists_colorFun {nc : ℕ} {k : PlaneMap} (hk : PlainMap k) (hnc : AtMostRegions nc k) :
    ∃ c : Point → ℕ, (∀ z ∈ cover k, c z < nc) ∧
      (∀ z ∈ cover k, ∀ t ∈ cover k, (c z = c t ↔ t ∈ k z)) := by
  obtain ⟨f, hf⟩ := hnc
  obtain ⟨c, hc⟩ : ∃ c : Point → ℕ, ∀ z, c z = sInf {i | i < nc ∧ z ∈ k (f i)} :=
    ⟨_, fun _ => rfl⟩
  have hmem : ∀ z ∈ cover k, c z < nc ∧ z ∈ k (f (c z)) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hf z hz
    rw [hc]
    exact Nat.sInf_mem (s := {i | i < nc ∧ z ∈ k (f i)}) ⟨i, hi, hzi⟩
  refine ⟨c, fun z hz => (hmem z hz).1, fun z hz t ht => ⟨fun heq => ?_, fun hrel => ?_⟩⟩
  · have h1 := (hmem z hz).2
    have h2 := (hmem t ht).2
    rw [← heq] at h2
    exact hk.trans _ _ (hk.symm _ _ h1) h2
  · have hreg : k t = k z := hk.region_eq hrel
    have hset : {i | i < nc ∧ z ∈ k (f i)} = {i | i < nc ∧ t ∈ k (f i)} := by
      ext i
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro _
      exact ⟨fun h => hk.symm _ _ (by rw [hreg]; exact hk.symm _ _ h),
        fun h => hk.symm _ _ (by rw [← hreg]; exact hk.symm _ _ h)⟩
    rw [hc, hc, hset]

/-- A colouring of the `n`-th partial map, read as a colour function: it is
constant on regions of `m` and separates adjacent regions, as long as both are
met by the first `n` grid points. -/
theorem exists_levelColoring {nc : ℕ} (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (hm : SimpleMap m) (n : ℕ) :
    ∃ c : Point → ℕ, (∀ z ∈ inPmap m n, c z < nc) ∧
      (∀ z ∈ inPmap m n, ∀ t ∈ inPmap m n, t ∈ m z → c z = c t) ∧
      (∀ z ∈ inPmap m n, ∀ t ∈ inPmap m n, Adjacent m z t → c z ≠ c t) := by
  obtain ⟨k, hcol, hnc⟩ := hfin _ (pmap_finiteSimpleMap hm n)
  obtain ⟨c, hlt, hiff⟩ := exists_colorFun hcol.plain hnc
  have hsub : ∀ z ∈ inPmap m n, z ∈ cover k := by
    intro z hz
    have hz' : z ∈ cover (pmap m n) := by rw [cover_pmap hm.plain]; exact hz
    exact hcol.consistent z hz'
  refine ⟨c, fun z hz => hlt z (hsub z hz), fun z hz t ht hmem => ?_, fun z hz t ht hadj => ?_⟩
  · exact (hiff z (hsub z hz) t (hsub t ht)).mpr (hcol.consistent z ⟨hz, ht, hmem⟩)
  · intro heq
    exact hcol.adjacent z t (adjacent_pmap hm.plain hadj hz ht)
      ((hiff z (hsub z hz) t (hsub t ht)).mp heq)

/-! ### The limit colouring -/

/-- **Compactness extension**: if every finite simple map can be coloured with
`nc` colours, then so can every simple map.  This is the reference's
`compactness_extension`. -/
theorem compactness_extension {nc : ℕ} (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    {m₀ : PlaneMap} (hm₀ : SimpleMap m₀) : ColorableWith nc m₀ := by
  classical
  -- A colouring of each partial map, as a colour function.
  choose c hc_lt hc_eq hc_ne using fun n => exists_levelColoring hfin hm₀ n
  -- Clamped colours of the grid points, so that they range over a finite set.
  obtain ⟨col, hcol_le, hcol_eq⟩ : ∃ col : ℕ → ℕ → ℕ, (∀ n i, col n i ≤ nc) ∧
      ∀ n i, c n (stdPoint i) < nc → col n i = c n (stdPoint i) :=
    ⟨fun n i => min (c n (stdPoint i)) nc, fun _ _ => min_le_right _ _,
      fun _ _ h => min_eq_left h.le⟩
  -- A limit colour for each grid point, via an ultrafilter refining `atTop`.
  set U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  have key : ∀ i : ℕ, ∃ v, {n | col n i = v} ∈ (U : Filter ℕ) := by
    intro i
    have huniv : (⋃ v ∈ (↑(Finset.range (nc + 1)) : Set ℕ), {n | col n i = v})
        ∈ (U : Filter ℕ) := by
      have hall : (⋃ v ∈ (↑(Finset.range (nc + 1)) : Set ℕ), {n | col n i = v}) = Set.univ := by
        ext n
        simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, Set.mem_ofPred_eq,
          Set.mem_univ, iff_true, exists_prop]
        exact ⟨col n i, Nat.lt_succ_of_le (hcol_le n i), rfl⟩
      rw [hall]
      exact Filter.univ_mem
    obtain ⟨v, -, hv⟩ :=
      (U.finite_biUnion_mem_iff (Finset.range (nc + 1)).finite_toSet).mp huniv
    exact ⟨v, hv⟩
  choose γ hγ using key
  -- Any two grid points get their limit colours simultaneously at some level.
  have pair : ∀ i j : ℕ, ∃ n, i < n ∧ j < n ∧ col n i = γ i ∧ col n j = γ j := by
    intro i j
    have h3 : {n : ℕ | max i j < n} ∈ (U : Filter ℕ) :=
      hU (Filter.eventually_gt_atTop (max i j))
    obtain ⟨n, ⟨hni, hnj⟩, hn3⟩ :=
      Filter.nonempty_of_mem (Filter.inter_mem (Filter.inter_mem (hγ i) (hγ j)) h3)
    exact ⟨n, lt_of_le_of_lt (le_max_left _ _) hn3, lt_of_le_of_lt (le_max_right _ _) hn3,
      hni, hnj⟩
  -- A grid point in the region of each covered point.
  have hidx0 : ∀ z : Point, ∃ i, z ∈ cover m₀ → stdPoint i ∈ m₀ z := by
    intro z
    by_cases hz : z ∈ cover m₀
    · obtain ⟨i, hi⟩ := exists_stdPoint_mem hm₀ hz
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose idx hidx using hidx0
  have hstd_in : ∀ {z : Point} {n : ℕ}, z ∈ cover m₀ → idx z < n →
      stdPoint (idx z) ∈ inPmap m₀ n :=
    fun hz hlt => ⟨_, hlt, hm₀.plain.mem_cover_right (hidx _ hz)⟩
  have hcol_std : ∀ {z : Point} {n : ℕ}, z ∈ cover m₀ → idx z < n →
      col n (idx z) = c n (stdPoint (idx z)) ∧ c n (stdPoint (idx z)) < nc := by
    intro z n hz hlt
    have hlt' := hc_lt n _ (hstd_in hz hlt)
    exact ⟨hcol_eq n _ hlt', hlt'⟩
  -- The limit colours are below `nc`, constant on regions, and separate
  -- adjacent regions.
  have hγ_lt : ∀ {z : Point}, z ∈ cover m₀ → γ (idx z) < nc := by
    intro z hz
    obtain ⟨n, hn1, -, hn3, -⟩ := pair (idx z) (idx z)
    obtain ⟨he, hlt⟩ := hcol_std hz hn1
    omega
  have hγ_eq : ∀ {z t : Point}, z ∈ cover m₀ → t ∈ m₀ z → γ (idx z) = γ (idx t) := by
    intro z t hz ht
    have htc : t ∈ cover m₀ := hm₀.plain.mem_cover_right ht
    obtain ⟨n, hn1, hn2, hn3, hn4⟩ := pair (idx z) (idx t)
    have hmem : stdPoint (idx t) ∈ m₀ (stdPoint (idx z)) := by
      have h1 : stdPoint (idx z) ∈ m₀ z := hidx z hz
      have h2 : stdPoint (idx t) ∈ m₀ t := hidx t htc
      rw [hm₀.plain.region_eq h1, ← hm₀.plain.region_eq ht]
      exact h2
    have heq := hc_eq n _ (hstd_in hz hn1) _ (hstd_in htc hn2) hmem
    obtain ⟨he1, -⟩ := hcol_std hz hn1
    obtain ⟨he2, -⟩ := hcol_std htc hn2
    omega
  have hγ_ne : ∀ {z t : Point}, z ∈ cover m₀ → t ∈ cover m₀ → Adjacent m₀ z t →
      γ (idx z) ≠ γ (idx t) := by
    intro z t hz ht hadj heq
    obtain ⟨n, hn1, hn2, hn3, hn4⟩ := pair (idx z) (idx t)
    have hadj' : Adjacent m₀ (stdPoint (idx z)) (stdPoint (idx t)) :=
      hadj.congr hm₀.plain (hidx z hz) (hidx t ht)
    have hne := hc_ne n _ (hstd_in hz hn1) _ (hstd_in ht hn2) hadj'
    obtain ⟨he1, -⟩ := hcol_std hz hn1
    obtain ⟨he2, -⟩ := hcol_std ht hn2
    omega
  -- The limit colouring: two covered points are related when their grid points
  -- have the same limit colour.
  refine ⟨fun z => {t | z ∈ cover m₀ ∧ t ∈ cover m₀ ∧ γ (idx z) = γ (idx t)},
    ⟨⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩,
      fun _ _ h _ hu => ⟨h.1, hu.2.1, h.2.2.trans hu.2.2⟩⟩,
     fun _ hz => hz.1,
     fun z t ht => ⟨hm₀.plain.mem_cover_left ht, hm₀.plain.mem_cover_right ht,
       hγ_eq (hm₀.plain.mem_cover_left ht) ht⟩,
     fun z t hadj hk => hγ_ne hk.1 hk.2.1 hadj hk.2.2⟩, ?_⟩
  -- At most `nc` colours: one representative point per limit colour.
  have hrep : ∀ v : ℕ, ∃ w : Point,
      (∃ w', w' ∈ cover m₀ ∧ γ (idx w') = v) → w ∈ cover m₀ ∧ γ (idx w) = v := by
    intro v
    by_cases h : ∃ w', w' ∈ cover m₀ ∧ γ (idx w') = v
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨(0, 0), fun h' => absurd h' h⟩
  choose f hf using hrep
  refine ⟨f, fun z hz => ⟨γ (idx z), hγ_lt hz.1, ?_⟩⟩
  obtain ⟨h1, h2⟩ := hf (γ (idx z)) ⟨z, hz.1, rfl⟩
  exact ⟨h1, hz.1, h2⟩

/-- The Four Colour Theorem for finite simple maps implies the Four Colour
Theorem. -/
theorem fourColorTheorem_of_finite (h : FourColorTheoremFinite) : FourColorTheorem :=
  fun _ hm => compactness_extension h hm

end FourColor

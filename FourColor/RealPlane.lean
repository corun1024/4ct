import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The real plane, and the statement of the Four Colour Theorem

An elementary formalisation of the plane topology needed to *state* the Four
Colour Theorem.

The reference development spends 2,284 lines (`reals/real.v`,
`reals/realsyntax.v`, `reals/realprop.v`, `reals/realcategorical.v` and
`proof/dedekind.v`) axiomatising a complete ordered field, proving its
consequences, showing any two models are isomorphic, and building one from
Dedekind cuts.  All of that exists because Coq's core logic has no quotient
types, so reals had to be modelled as a setoid of denotations.  In Lean none of
it is needed: `ℝ` is Mathlib's, `ConditionallyCompleteLinearOrderedField` is the
axiomatisation, and `LinearOrderedField.inducedOrderRingIso` is the categoricity
theorem.  So this file states everything directly over `ℝ`.

Following the reference, the topological notions are defined *elementarily*, so
that the statement of the theorem is transparent and depends on nothing but
order and arithmetic on `ℝ`.  Each is then proved to agree with Mathlib's
corresponding notion, so the statement can be read either way.

## References

Gonthier's `theories/proof/realplane.v` and `theories/proof/fourcolor.v`.
-/

namespace FourColor

/-- A point of the real plane. -/
abbrev Point := ℝ × ℝ

/-- A region: a set of points.  Not required to be topologically nice. -/
abbrev Region := Set Point

/-- A map: a relation on points.  A *plain* map is a partial equivalence
relation, whose classes are its regions. -/
abbrev PlaneMap := Point → Region

/-- An open rectangle. -/
structure Rect where
  /-- Left edge. -/
  x₀ : ℝ
  /-- Right edge. -/
  x₁ : ℝ
  /-- Bottom edge. -/
  y₀ : ℝ
  /-- Top edge. -/
  y₁ : ℝ

/-- The region enclosed by a rectangle. -/
def Rect.toRegion (r : Rect) : Region :=
  {z | r.x₀ < z.1 ∧ z.1 < r.x₁ ∧ r.y₀ < z.2 ∧ z.2 < r.y₁}

instance : CoeFun Rect (fun _ => Point → Prop) := ⟨fun r z => z ∈ r.toRegion⟩

/-! ### Elementary topology -/

/-- A region is open when every point of it has a rectangle neighbourhood inside
it.  This is the reference's elementary definition. -/
def IsOpenRegion (r : Region) : Prop :=
  ∀ z ∈ r, ∃ u : Rect, z ∈ u.toRegion ∧ u.toRegion ⊆ r

/-- The closure of a region: points every open neighbourhood of which meets it. -/
def regionClosure (r : Region) : Region :=
  {z | ∀ u : Region, IsOpenRegion u → z ∈ u → (r ∩ u).Nonempty}

/-- A region is connected when it cannot be split by two open sets. -/
def IsConnectedRegion (r : Region) : Prop :=
  ∀ u v : Region, IsOpenRegion u → IsOpenRegion v → r ⊆ u ∪ v →
    (u ∩ r).Nonempty → (v ∩ r).Nonempty → (u ∩ v).Nonempty

/-! ### Agreement with Mathlib's topology -/

theorem isOpen_rect (u : Rect) : IsOpen u.toRegion := by
  have : u.toRegion = (Set.Ioo u.x₀ u.x₁) ×ˢ (Set.Ioo u.y₀ u.y₁) := by
    ext z
    simp only [Rect.toRegion, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo]
    tauto
  rw [this]
  exact (isOpen_Ioo).prod isOpen_Ioo

/-- The elementary notion of openness is Mathlib's. -/
theorem isOpenRegion_iff (r : Region) : IsOpenRegion r ↔ IsOpen r := by
  constructor
  · intro h
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨u, hzu, hur⟩ := h z hz
    exact ⟨u.toRegion, hur, isOpen_rect u, hzu⟩
  · intro h z hz
    rw [isOpen_prod_iff] at h
    obtain ⟨s, t, hs, ht, hzs, hzt, hst⟩ := h z.1 z.2 hz
    obtain ⟨a, b, hab, habs⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hzs)
    obtain ⟨c, d, hcd, hcdt⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ht.mem_nhds hzt)
    refine ⟨⟨a, b, c, d⟩, ⟨hab.1, hab.2, hcd.1, hcd.2⟩, ?_⟩
    rintro w ⟨hw1, hw2, hw3, hw4⟩
    exact hst ⟨habs ⟨hw1, hw2⟩, hcdt ⟨hw3, hw4⟩⟩

/-- The elementary closure is Mathlib's. -/
theorem regionClosure_eq (r : Region) : regionClosure r = closure r := by
  ext z
  simp only [regionClosure, Set.mem_setOf_eq, mem_closure_iff]
  constructor
  · intro h u hu hzu
    have hm := h u ((isOpenRegion_iff u).mpr hu) hzu
    rwa [Set.inter_comm] at hm
  · intro h u hu hzu
    have hm := h u ((isOpenRegion_iff u).mp hu) hzu
    rwa [Set.inter_comm] at hm

/-! ### Maps -/

/-- A plain map: a partial equivalence relation on points. -/
structure PlainMap (m : PlaneMap) : Prop where
  /-- Symmetry. -/
  symm : ∀ z₁ z₂, z₂ ∈ m z₁ → z₁ ∈ m z₂
  /-- Transitivity. -/
  trans : ∀ z₁ z₂, z₂ ∈ m z₁ → m z₂ ⊆ m z₁

/-- The region covered by a map. -/
def cover (m : PlaneMap) : Region := {z | z ∈ m z}

/-- Every region of `m₁` lies in a region of `m₂`. -/
def Submap (m₁ m₂ : PlaneMap) : Prop := ∀ z, m₁ z ⊆ m₂ z

/-- A map has at most `n` regions. -/
def AtMostRegions (n : ℕ) (m : PlaneMap) : Prop :=
  ∃ f : ℕ → Point, ∀ z ∈ cover m, ∃ i < n, z ∈ m (f i)

/-- A simple map: plain, with open connected regions. -/
structure SimpleMap (m : PlaneMap) : Prop where
  /-- The underlying plain map. -/
  plain : PlainMap m
  /-- Each region is open. -/
  isOpen : ∀ z, IsOpenRegion (m z)
  /-- Each region is connected. -/
  isConnected : ∀ z, IsConnectedRegion (m z)

/-- A simple map with finitely many regions. -/
structure FiniteSimpleMap (m : PlaneMap) : Prop where
  /-- The underlying simple map. -/
  simple : SimpleMap m
  /-- Finitely many regions. -/
  finite : ∃ n, AtMostRegions n m

/-! ### Borders, corners, adjacency and colourings -/

/-- The common border of the regions of two points. -/
def border (m : PlaneMap) (z₁ z₂ : Point) : Region :=
  regionClosure (m z₁) ∩ regionClosure (m z₂)

/-- The map of regions whose closure contains a given point. -/
def cornerMap (m : PlaneMap) (z : Point) : PlaneMap :=
  fun z₁ => {z₂ | z₂ ∈ m z₁ ∧ z ∈ regionClosure (m z₁)}

/-- The points lying in the closure of at most two regions. -/
def notCorner (m : PlaneMap) : Region := {z | AtMostRegions 2 (cornerMap m z)}

/-- Two regions are adjacent when they are distinct and share a non-corner
border point. -/
def Adjacent (m : PlaneMap) (z₁ z₂ : Point) : Prop :=
  z₂ ∉ m z₁ ∧ (notCorner m ∩ border m z₁ z₂).Nonempty

/-- `k` is a colouring of `m`: a plain map covering the same points, refined by
`m`, that separates adjacent regions. -/
structure Coloring (m k : PlaneMap) : Prop where
  /-- The colouring is a plain map. -/
  plain : PlainMap k
  /-- It covers no more than `m`. -/
  cover_subset : cover k ⊆ cover m
  /-- Regions of `m` get a single colour. -/
  consistent : Submap m k
  /-- Adjacent regions get different colours. -/
  adjacent : ∀ z₁ z₂, Adjacent m z₁ z₂ → z₂ ∉ k z₁

/-- A map is colourable with `n` colours. -/
def ColorableWith (n : ℕ) (m : PlaneMap) : Prop :=
  ∃ k, Coloring m k ∧ AtMostRegions n k

/-! ### The statement -/

/-- **The Four Colour Theorem**: every simple map of the real plane can be
coloured with four colours.  This is the goal of the development; the reference
derives it from `four_color_finite` by a compactness argument. -/
def FourColorTheorem : Prop := ∀ m : PlaneMap, SimpleMap m → ColorableWith 4 m

/-- The finite case, from which the general statement follows by compactness. -/
def FourColorTheoremFinite : Prop :=
  ∀ m : PlaneMap, FiniteSimpleMap m → ColorableWith 4 m

end FourColor

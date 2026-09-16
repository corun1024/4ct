import FourColor.Hypermap
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Data.Int.Interval

/-!
# Grid geometry

Geometry over an integer grid: raster graphics.  A `GPoint` denotes, according
to context, a grid point, a grid *pixel* (named by its lower-left vertex), or a
grid *dart* (a pixel corner: the subpixel of the bisected grid containing the
chosen vertex).  A dart also denotes the directed pixel edge starting at its
vertex and running counterclockwise around its pixel.

The reference builds a `zmodType` on a bespoke `gpoint` record; here `GPoint` is
`ℤ × ℤ` and Mathlib's group structure serves directly.  Likewise `halfg` and
`oddg` are Lean's `Int` division and modulus, which are Euclidean, so the
defining identity `halfg d + halfg d + oddg d = d` is `Int.ediv_add_emod`.

The three dart maps form a genuine `Hypermap` on `GPoint` — an infinite one,
which is fine since `Hypermap` never required finiteness.

## References

Gonthier's `theories/proof/grid.v`.
-/

namespace FourColor

/-- A grid point, pixel, or dart. -/
abbrev GPoint := ℤ × ℤ

/-- The pixel of which a dart is a corner. -/
def halfg (d : GPoint) : GPoint := (d.1 / 2, d.2 / 2)

/-- The unit-square vertex congruent to the vertex of a dart. -/
def oddg (d : GPoint) : GPoint := (d.1 % 2, d.2 % 2)

/-- The four vertices of the unit square. -/
def IsOddg (c : GPoint) : Prop := (c.1 = 0 ∨ c.1 = 1) ∧ (c.2 = 0 ∨ c.2 = 1)

/-- The counterclockwise quarter turn permuting the unit-square corners. -/
def ccw (p : GPoint) : GPoint := (1 - p.2, p.1)

/-- The chord from `c` to `ccw c`. -/
def arcg (c : GPoint) : GPoint := ccw c - c

/-- The start vertex of a dart, shared with its pixel. -/
def end0g (d : GPoint) : GPoint := halfg d + oddg d

/-- The end vertex of the directed edge a dart denotes. -/
def end1g (d : GPoint) : GPoint := halfg d + ccw (oddg d)

/-- The next dart counterclockwise around the same pixel. -/
def gface (d : GPoint) : GPoint := d + arcg (oddg d)

/-- The next dart at the same grid point. -/
def gnode (d : GPoint) : GPoint := d - arcg (oddg d)

/-- The dart denoting the opposite edge. -/
def gedge (d : GPoint) : GPoint := d + (arcg (oddg d) - arcg (ccw (oddg d)))

/-! ### Halves and parities -/

theorem halfgK (d : GPoint) : halfg d + halfg d + oddg d = d := by
  obtain ⟨x, y⟩ := d
  simp only [halfg, oddg, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> omega

theorem oddgP (d : GPoint) : IsOddg (oddg d) := by
  obtain ⟨x, y⟩ := d
  exact ⟨by have := Int.emod_two_eq_zero_or_one x; simpa [oddg] using this,
    by have := Int.emod_two_eq_zero_or_one y; simpa [oddg] using this⟩

theorem oddg_add_self (p d : GPoint) : oddg (p + p + d) = oddg d := by
  obtain ⟨a, b⟩ := p; obtain ⟨x, y⟩ := d
  simp only [oddg, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> omega

theorem halfg_add_self (p d : GPoint) : halfg (p + p + d) = p + halfg d := by
  obtain ⟨a, b⟩ := p; obtain ⟨x, y⟩ := d
  simp only [halfg, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> omega

@[simp] theorem halfg_double (p : GPoint) : halfg (p + p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [halfg, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> omega

@[simp] theorem oddg_double (p : GPoint) : oddg (p + p) = 0 := by
  obtain ⟨x, y⟩ := p
  simp only [oddg, Prod.mk_add_mk, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  constructor <;> omega

theorem oddg_of_isOddg {c : GPoint} (hc : IsOddg c) : oddg c = c := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> rfl

theorem halfg_of_isOddg {c : GPoint} (hc : IsOddg c) : halfg c = 0 := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> rfl

theorem oddg_eq {p c : GPoint} (hc : IsOddg c) : oddg (p + p + c) = c := by
  rw [oddg_add_self, oddg_of_isOddg hc]

theorem halfg_eq {p c : GPoint} (hc : IsOddg c) : halfg (p + p + c) = p := by
  rw [halfg_add_self, halfg_of_isOddg hc, add_zero]

/-! ### The quarter turn -/

theorem isOddg_ccw {c : GPoint} (hc : IsOddg c) : IsOddg (ccw c) := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;>
    exact ⟨by norm_num [ccw], by norm_num [ccw]⟩

theorem ccw4 (p : GPoint) : ccw (ccw (ccw (ccw p))) = p := by
  obtain ⟨x, y⟩ := p
  simp only [ccw, Prod.mk.injEq]
  constructor <;> ring

theorem ccw2 (p : GPoint) : ccw (ccw p) = ((1 : ℤ), (1 : ℤ)) - p := by
  obtain ⟨x, y⟩ := p
  rfl

/-! ### The dart maps -/

theorem gface_eq (d : GPoint) : gface d = halfg d + halfg d + ccw (oddg d) := by
  have h := halfgK d
  rw [gface, arcg]
  nth_rewrite 1 [← h]
  abel

theorem oddg_gface (d : GPoint) : oddg (gface d) = ccw (oddg d) := by
  rw [gface_eq, oddg_eq (isOddg_ccw (oddgP d))]

theorem halfg_gface (d : GPoint) : halfg (gface d) = halfg d := by
  rw [gface_eq, halfg_eq (isOddg_ccw (oddgP d))]

theorem gface4 (d : GPoint) : gface (gface (gface (gface d))) = d := by
  rw [gface_eq (gface (gface (gface d))), halfg_gface, halfg_gface, halfg_gface,
    oddg_gface, oddg_gface, oddg_gface, ccw4]
  exact halfgK d

theorem gnode_eq (d : GPoint) : gnode d = halfg d + halfg d + oddg d - arcg (oddg d) := by
  rw [gnode, halfgK]

/-- `gnode ∘ gface = gedge`: the triangular identity in the form the reference
proves it. -/
theorem gnode_gface (d : GPoint) : gnode (gface d) = gedge d := by
  rw [gnode, oddg_gface, gface, gedge]
  abel

theorem arcg_ccw2 {c : GPoint} (hc : IsOddg c) : arcg (ccw (ccw c)) = - arcg c := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> rfl

theorem arcg_sum {c : GPoint} (hc : IsOddg c) :
    arcg c + arcg (ccw c) + arcg (ccw (ccw c)) + arcg (ccw (ccw (ccw c))) = 0 := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> rfl

theorem gnode_eq' (d : GPoint) :
    gnode d = (halfg d - arcg (oddg d)) + (halfg d - arcg (oddg d)) + ccw (oddg d) := by
  have h := halfgK d
  rw [gnode, arcg]
  nth_rewrite 1 [← h]
  abel

theorem oddg_gnode (d : GPoint) : oddg (gnode d) = ccw (oddg d) := by
  rw [gnode_eq', oddg_eq (isOddg_ccw (oddgP d))]

theorem halfg_gnode (d : GPoint) : halfg (gnode d) = halfg d - arcg (oddg d) := by
  rw [gnode_eq', halfg_eq (isOddg_ccw (oddgP d))]

theorem gnode4 (d : GPoint) : gnode (gnode (gnode (gnode d))) = d := by
  have hs := arcg_sum (oddgP d)
  have h := halfgK d
  rw [gnode_eq' (gnode (gnode (gnode d)))]
  simp only [halfg_gnode, oddg_gnode, ccw4]
  have hz : halfg d - arcg (oddg d) - arcg (ccw (oddg d)) - arcg (ccw (ccw (oddg d)))
      - arcg (ccw (ccw (ccw (oddg d)))) = halfg d := by
    rw [show halfg d - arcg (oddg d) - arcg (ccw (oddg d)) - arcg (ccw (ccw (oddg d)))
        - arcg (ccw (ccw (ccw (oddg d))))
      = halfg d - (arcg (oddg d) + arcg (ccw (oddg d)) + arcg (ccw (ccw (oddg d)))
        + arcg (ccw (ccw (ccw (oddg d))))) from by abel, hs, sub_zero]
  rw [hz]
  exact h

theorem oddg_gedge (d : GPoint) : oddg (gedge d) = ccw (ccw (oddg d)) := by
  rw [← gnode_gface, oddg_gnode, oddg_gface]

theorem halfg_gedge (d : GPoint) : halfg (gedge d) = halfg d - arcg (ccw (oddg d)) := by
  rw [← gnode_gface, halfg_gnode, oddg_gface, halfg_gface]

theorem gedge_eq (d : GPoint) :
    gedge d = (halfg d - arcg (ccw (oddg d))) + (halfg d - arcg (ccw (oddg d)))
      + ccw (ccw (oddg d)) := by
  rw [← gnode_gface, gnode_eq', oddg_gface, halfg_gface]

theorem gedge2 (d : GPoint) : gedge (gedge d) = d := by
  have h := halfgK d
  have hopp : arcg (ccw (ccw (ccw (oddg d)))) = - arcg (ccw (oddg d)) :=
    arcg_ccw2 (isOddg_ccw (oddgP d))
  rw [gedge_eq (gedge d), halfg_gedge, oddg_gedge, ccw4, hopp]
  rw [show halfg d - arcg (ccw (oddg d)) - -arcg (ccw (oddg d)) = halfg d from by abel]
  exact h

/-! ### The grid hypermap -/

/-- `gface` as a permutation. -/
def gfacePerm : Equiv.Perm GPoint where
  toFun := gface
  invFun := fun d => gface (gface (gface d))
  left_inv := gface4
  right_inv := fun d => gface4 d

/-- `gnode` as a permutation. -/
def gnodePerm : Equiv.Perm GPoint where
  toFun := gnode
  invFun := fun d => gnode (gnode (gnode d))
  left_inv := gnode4
  right_inv := fun d => gnode4 d

/-- `gedge` as a permutation; it is an involution. -/
def gedgePerm : Equiv.Perm GPoint where
  toFun := gedge
  invFun := gedge
  left_inv := gedge2
  right_inv := gedge2

/-- The infinite hypermap of grid darts: its faces are the pixels and its nodes
are the grid points. -/
def gridHypermap : Hypermap GPoint where
  edge := gedgePerm
  node := gnodePerm
  face := gfacePerm
  node_face_edge := Equiv.ext fun d => by
    show gnode (gface (gedge d)) = d
    rw [gnode_gface, gedge2]

/-! ### Grid rectangles -/

/-- A rectangular set of pixels. -/
structure GRect where
  /-- Left bound (inclusive). -/
  xmin : ℤ
  /-- Right bound (exclusive). -/
  xmax : ℤ
  /-- Bottom bound (inclusive). -/
  ymin : ℤ
  /-- Top bound (exclusive). -/
  ymax : ℤ

/-- The pixels of a rectangle. -/
def GRect.toRegion (r : GRect) : Set GPoint :=
  {p | r.xmin ≤ p.1 ∧ p.1 < r.xmax ∧ r.ymin ≤ p.2 ∧ p.2 < r.ymax}

@[simp] theorem GRect.mem_toRegion (r : GRect) (p : GPoint) :
    p ∈ r.toRegion ↔ r.xmin ≤ p.1 ∧ p.1 < r.xmax ∧ r.ymin ≤ p.2 ∧ p.2 < r.ymax :=
  Iff.rfl

/-- The smallest rectangle containing both `r` and the pixel `p`. -/
def extendGRect (p : GPoint) (r : GRect) : GRect :=
  ⟨min r.xmin p.1, max r.xmax (p.1 + 1), min r.ymin p.2, max r.ymax (p.2 + 1)⟩

theorem mem_extendGRect_self (p : GPoint) (r : GRect) :
    p ∈ (extendGRect p r).toRegion := by
  refine ⟨min_le_right _ _, ?_, min_le_right _ _, ?_⟩ <;>
    exact lt_of_lt_of_le (by omega) (le_max_right _ _)

theorem subset_extendGRect (p : GPoint) (r : GRect) :
    r.toRegion ⊆ (extendGRect p r).toRegion := by
  rintro q ⟨h1, h2, h3, h4⟩
  exact ⟨le_trans (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_left _ _),
    le_trans (min_le_left _ _) h3, lt_of_lt_of_le h4 (le_max_left _ _)⟩

/-! ### Dimensions -/

/-- The number of integers in `[a, b)`. -/
def zwidth (a b : ℤ) : ℕ := (b - a).toNat

/-- The pixel width of a rectangle. -/
def GRect.width (r : GRect) : ℕ := zwidth r.xmin r.xmax

/-- The pixel height of a rectangle. -/
def GRect.height (r : GRect) : ℕ := zwidth r.ymin r.ymax

/-- The number of pixels in a rectangle. -/
def GRect.area (r : GRect) : ℕ := r.width * r.height

/-- A rectangle is proper when it is nonempty. -/
def GRect.Proper (r : GRect) : Prop := 0 < r.area

theorem zwidth_pos_iff (a b : ℤ) : 0 < zwidth a b ↔ a < b := by
  simp only [zwidth]
  omega

theorem GRect.proper_iff (r : GRect) :
    r.Proper ↔ (r.xmin < r.xmax ∧ r.ymin < r.ymax) := by
  simp only [Proper, area, width, height]
  constructor
  · intro h
    have hx : 0 < zwidth r.xmin r.xmax := by
      rcases Nat.eq_zero_or_pos (zwidth r.xmin r.xmax) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    have hy : 0 < zwidth r.ymin r.ymax := by
      rcases Nat.eq_zero_or_pos (zwidth r.ymin r.ymax) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    exact ⟨(zwidth_pos_iff _ _).mp hx, (zwidth_pos_iff _ _).mp hy⟩
  · rintro ⟨hx, hy⟩
    exact Nat.mul_pos ((zwidth_pos_iff _ _).mpr hx) ((zwidth_pos_iff _ _).mpr hy)

/-- A rectangle is proper exactly when it contains a pixel. -/
theorem GRect.proper_iff_nonempty (r : GRect) : r.Proper ↔ r.toRegion.Nonempty := by
  rw [proper_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨(r.xmin, r.ymin), le_rfl, hx, le_rfl, hy⟩
  · rintro ⟨p, h1, h2, h3, h4⟩
    exact ⟨lt_of_le_of_lt h1 h2, lt_of_le_of_lt h3 h4⟩

/-! ### Insets and neighbourhoods -/

/-- The rectangle with a one-pixel border removed. -/
def GRect.inset (r : GRect) : GRect := ⟨r.xmin + 1, r.xmax - 1, r.ymin + 1, r.ymax - 1⟩

/-- The 3×3 rectangle of pixels touching a pixel. -/
def gtouch (p : GPoint) : GRect := ⟨p.1 - 1, p.1 + 2, p.2 - 1, p.2 + 2⟩

/-- The 2×2 rectangle of pixels touching a grid point. -/
def ltouch (q : GPoint) : GRect := ⟨q.1 - 1, q.1 + 1, q.2 - 1, q.2 + 1⟩

/-- The inset is exactly the set of pixels all of whose neighbours lie in `r`. -/
theorem GRect.mem_inset_iff (r : GRect) (p : GPoint) :
    p ∈ r.inset.toRegion ↔ (gtouch p).toRegion ⊆ r.toRegion := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ q ⟨g1, g2, g3, g4⟩
    simp only [inset, gtouch] at *
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro h
    have h1 := h (show ((p.1 - 1, p.2 - 1) : GPoint) ∈ (gtouch p).toRegion by
      simp only [gtouch, GRect.mem_toRegion]; omega)
    have h2 := h (show ((p.1 + 1, p.2 + 1) : GPoint) ∈ (gtouch p).toRegion by
      simp only [gtouch, GRect.mem_toRegion]; omega)
    simp only [inset, GRect.mem_toRegion] at *
    omega

/-! ### Refinement -/

/-- The rectangle of subpixels, in the binary subdivision. -/
def refineRect (r : GRect) : GRect :=
  ⟨r.xmin + r.xmin, r.xmax + r.xmax, r.ymin + r.ymin, r.ymax + r.ymax⟩

theorem mem_refineRect (r : GRect) (p : GPoint) :
    p ∈ (refineRect r).toRegion ↔ halfg p ∈ r.toRegion := by
  simp only [refineRect, GRect.mem_toRegion, halfg]
  omega

theorem zwidth_double (a b : ℤ) : zwidth (a + a) (b + b) = 2 * zwidth a b := by
  simp only [zwidth]
  omega

theorem area_refineRect (r : GRect) : (refineRect r).area = 4 * r.area := by
  simp only [GRect.area, GRect.width, GRect.height, refineRect, zwidth_double]
  ring

theorem proper_refineRect (r : GRect) : (refineRect r).Proper ↔ r.Proper := by
  simp only [GRect.Proper, area_refineRect]
  omega

theorem refine_inset (r : GRect) :
    refineRect r.inset = (refineRect r).inset.inset := by
  simp only [refineRect, GRect.inset, GRect.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-! ### Half-planes

`gchop d` is the closed half-plane bounded by the line through the edge that the
dart `d` denotes, on the side containing `d`'s pixel.
-/

/-- The half-plane delimited by the edge of a dart, containing its pixel. -/
def gchop (d : GPoint) : Set GPoint :=
  if (oddg d).1 = 0 then
    (if (oddg d).2 = 0 then {p | (halfg d).2 ≤ p.2} else {p | (halfg d).1 ≤ p.1})
  else
    (if (oddg d).2 = 0 then {p | p.1 ≤ (halfg d).1} else {p | p.2 ≤ (halfg d).2})

theorem gchop_halfg (d : GPoint) : halfg d ∈ gchop d := by
  simp only [gchop]
  split <;> split <;> simp

theorem arcg_ccw_eq {c : GPoint} (hc : IsOddg c) :
    arcg (ccw c) = (if c.1 = 0 then (if c.2 = 0 then ((0 : ℤ), (1 : ℤ)) else (1, 0))
      else (if c.2 = 0 then (-1, 0) else (0, -1))) := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> simp [arcg, ccw]

/-- The edge dart chops the complementary half-plane. -/
theorem gchop_gedge (d : GPoint) (p : GPoint) : p ∈ gchop (gedge d) ↔ p ∉ gchop d := by
  have hodd : oddg (gedge d) = ((1 : ℤ), (1 : ℤ)) - oddg d := by rw [oddg_gedge, ccw2]
  have hhalf := halfg_gedge d
  have harc := arcg_ccw_eq (oddgP d)
  obtain ⟨hx | hx, hy | hy⟩ := oddgP d
  · have h1 : (oddg (gedge d)).1 = 1 := by rw [hodd]; simp [hx]
    have h2 : (oddg (gedge d)).2 = 1 := by rw [hodd]; simp [hy]
    have h3 : (halfg (gedge d)).2 = (halfg d).2 - 1 := by
      rw [hhalf, harc, if_pos hx, if_pos hy]; rfl
    simp only [gchop, h1, h2, hx, hy, h3, Set.mem_setOf_eq, if_pos, if_neg, one_ne_zero,
      if_false, if_true]
    omega
  · have h1 : (oddg (gedge d)).1 = 1 := by rw [hodd]; simp [hx]
    have h2 : (oddg (gedge d)).2 = 0 := by rw [hodd]; simp [hy]
    have h3 : (halfg (gedge d)).1 = (halfg d).1 - 1 := by
      rw [hhalf, harc, if_pos hx, if_neg (by omega : ¬((oddg d).2 = 0))]; rfl
    simp only [gchop, h1, h2, hx, hy, h3, Set.mem_setOf_eq, one_ne_zero, if_false, if_true]
    omega
  · have h1 : (oddg (gedge d)).1 = 0 := by rw [hodd]; simp [hx]
    have h2 : (oddg (gedge d)).2 = 1 := by rw [hodd]; simp [hy]
    have h3 : (halfg (gedge d)).1 = (halfg d).1 + 1 := by
      rw [hhalf, harc, if_neg (by omega : ¬((oddg d).1 = 0)), if_pos hy]
      simp only [Prod.fst_sub]
      omega
    simp only [gchop, h1, h2, hx, hy, h3, Set.mem_setOf_eq, one_ne_zero, if_false, if_true]
    omega
  · have h1 : (oddg (gedge d)).1 = 0 := by rw [hodd]; simp [hx]
    have h2 : (oddg (gedge d)).2 = 0 := by rw [hodd]; simp [hy]
    have h3 : (halfg (gedge d)).2 = (halfg d).2 + 1 := by
      rw [hhalf, harc, if_neg (by omega : ¬((oddg d).1 = 0)),
        if_neg (by omega : ¬((oddg d).2 = 0))]
      simp only [Prod.snd_sub]
      omega
    simp only [gchop, h1, h2, hx, hy, h3, Set.mem_setOf_eq, one_ne_zero, if_false, if_true]
    omega

/-- The half-plane one pixel further out. -/
def gchop1 (d : GPoint) : Set GPoint := gchop (gface (gface (gedge d)))

/-- The rectangle obtained by chopping `r` with the half-plane of `d`. -/
def gchopRect (r : GRect) (d : GPoint) : GRect :=
  if (oddg d).1 = 0 then
    (if (oddg d).2 = 0 then ⟨r.xmin, r.xmax, max r.ymin (halfg d).2, r.ymax⟩
     else ⟨max r.xmin (halfg d).1, r.xmax, r.ymin, r.ymax⟩)
  else
    (if (oddg d).2 = 0 then ⟨r.xmin, min r.xmax ((halfg d).1 + 1), r.ymin, r.ymax⟩
     else ⟨r.xmin, r.xmax, r.ymin, min r.ymax ((halfg d).2 + 1)⟩)

theorem mem_gchopRect (r : GRect) (d : GPoint) (p : GPoint) :
    p ∈ (gchopRect r d).toRegion ↔ p ∈ r.toRegion ∧ p ∈ gchop d := by
  obtain ⟨hx | hx, hy | hy⟩ := oddgP d <;>
    simp only [gchopRect, gchop, hx, hy, GRect.mem_toRegion, Set.mem_setOf_eq,
      max_le_iff, lt_min_iff, one_ne_zero, if_false, if_true] <;>
    constructor <;> intro h <;> omega

theorem gchopRect_subset (r : GRect) (d : GPoint) :
    (gchopRect r d).toRegion ⊆ r.toRegion := fun _ hp => ((mem_gchopRect r d _).mp hp).1

/-- The rectangle chopped by the wider half-plane. -/
def gchop1Rect (r : GRect) (d : GPoint) : GRect := gchopRect r (gface (gface (gedge d)))

theorem mem_gchop1Rect (r : GRect) (d : GPoint) (p : GPoint) :
    p ∈ (gchop1Rect r d).toRegion ↔ p ∈ r.toRegion ∧ p ∈ gchop1 d :=
  mem_gchopRect r _ p

/-! ### Enumeration and area monotonicity -/

/-- The pixels of a rectangle, as a finite set. -/
def GRect.toFinset (r : GRect) : Finset GPoint :=
  (Finset.Ico r.xmin r.xmax) ×ˢ (Finset.Ico r.ymin r.ymax)

@[simp] theorem GRect.mem_toFinset (r : GRect) (p : GPoint) :
    p ∈ r.toFinset ↔ p ∈ r.toRegion := by
  simp only [toFinset, Finset.mem_product, Finset.mem_Ico, mem_toRegion]
  tauto

/-- The area of a rectangle is the number of pixels it contains. -/
@[simp] theorem GRect.card_toFinset (r : GRect) : r.toFinset.card = r.area := by
  simp only [toFinset, Finset.card_product, Int.card_Ico, area, width, height, zwidth]

/-- A subrectangle has no larger area. -/
theorem area_le_of_subset {r s : GRect} (h : r.toRegion ⊆ s.toRegion) : r.area ≤ s.area := by
  rw [← GRect.card_toFinset, ← GRect.card_toFinset]
  exact Finset.card_le_card fun p hp =>
    (GRect.mem_toFinset s p).mpr (h ((GRect.mem_toFinset r p).mp hp))

/-- A strictly smaller subrectangle has strictly smaller area. -/
theorem area_lt_of_ssubset {r s : GRect} {p : GPoint} (h : r.toRegion ⊆ s.toRegion)
    (hps : p ∈ s.toRegion) (hpr : p ∉ r.toRegion) : r.area < s.area := by
  rw [← GRect.card_toFinset, ← GRect.card_toFinset]
  refine Finset.card_lt_card ⟨fun q hq =>
    (GRect.mem_toFinset s q).mpr (h ((GRect.mem_toFinset r q).mp hq)), ?_⟩
  intro hsub
  exact hpr ((GRect.mem_toFinset r p).mp (hsub ((GRect.mem_toFinset s p).mpr hps)))

/-! ### Vertices along a pixel -/

theorem end0g_gface (d : GPoint) : end0g (gface d) = end1g d := by
  rw [end0g, halfg_gface, oddg_gface, end1g]

theorem halfg_iter_gface (i : ℕ) (d : GPoint) : halfg (gface^[i] d) = halfg d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', halfg_gface, ih]

theorem oddg_iter_gface (i : ℕ) (d : GPoint) : oddg (gface^[i] d) = ccw^[i] (oddg d) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', oddg_gface, ih, Function.iterate_succ_apply']

theorem arcg_ccw_ne_zero {c : GPoint} (hc : IsOddg c) : arcg (ccw c) ≠ 0 := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> decide

/-- A dart and its edge dart lie in different pixels. -/
theorem halfg_gedge_ne (d : GPoint) : halfg (gedge d) ≠ halfg d := by
  rw [halfg_gedge]
  intro hc
  exact arcg_ccw_ne_zero (oddgP d) (sub_eq_self.mp hc)

/-- The unit-square corners form a single `ccw` orbit. -/
theorem exists_iter_ccw {c c' : GPoint} (hc : IsOddg c) (hc' : IsOddg c') :
    ∃ i < 4, ccw^[i] c = c' := by
  obtain ⟨x, y⟩ := c
  obtain ⟨x', y'⟩ := c'
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> rcases hc' with ⟨hx' | hx', hy' | hy'⟩ <;>
    subst hx <;> subst hy <;> subst hx' <;> subst hy' <;>
    first
      | exact ⟨0, by norm_num, by decide⟩
      | exact ⟨1, by norm_num, by decide⟩
      | exact ⟨2, by norm_num, by decide⟩
      | exact ⟨3, by norm_num, by decide⟩

/-- Two darts in the same pixel differ by a rotation. -/
theorem exists_iter_gface {d₁ d₂ : GPoint} (h : halfg d₁ = halfg d₂) :
    ∃ i < 4, gface^[i] d₁ = d₂ := by
  obtain ⟨i, hi, hci⟩ := exists_iter_ccw (oddgP d₁) (oddgP d₂)
  refine ⟨i, hi, ?_⟩
  have h1 := halfgK (gface^[i] d₁)
  have h2 := halfgK d₂
  rw [halfg_iter_gface, oddg_iter_gface, hci, h] at h1
  exact h1.symm.trans h2

/-! ### Chopping, shifting and insets

The lemmas below support the matte extension construction.  They relate the
half-plane of a dart to the wider half-plane `gchop1`, describe `gtouch` as the
intersection of four wide half-planes, and record how insets and chopped
rectangles behave under `gedge`.
-/

theorem gface_def (d : GPoint) : gface d = d + arcg (oddg d) := rfl

theorem gnode_def (d : GPoint) : gnode d = d - arcg (oddg d) := rfl

theorem gedge_def (d : GPoint) : gedge d = d + (arcg (oddg d) - arcg (ccw (oddg d))) := rfl

/-- `gnode` is injective. -/
theorem gnode_injective : Function.Injective gnode := by
  intro a b h
  have h4 : gnode (gnode (gnode (gnode a))) = gnode (gnode (gnode (gnode b))) := by
    rw [show gnode a = gnode b from h]
  rwa [gnode4, gnode4] at h4

/-- Crossing the edge of `gnode d` and turning once returns to `d`. -/
theorem gface_gedge_gnode (d : GPoint) : gface (gedge (gnode d)) = d := by
  refine gnode_injective ?_
  rw [gnode_gface, gedge2]

/-- The half-plane of a dart is contained in the wider half-plane. -/
theorem gchop_subset_gchop1 (d : GPoint) : gchop d ⊆ gchop1 d := by
  intro q hq
  revert hq
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gchop1, gchop, halfg_gface, oddg_gface, halfg_gedge, oddg_gedge, arcg, ccw,
      hx, hy] <;> omega

/-- The neighbourhood of a pixel is the intersection of the four wide
half-planes of the darts of that pixel. -/
theorem mem_gtouch_iff_chop1 (d q : GPoint) :
    q ∈ (gtouch (halfg d)).toRegion ↔
      q ∈ gchop1 d ∧ q ∈ gchop1 (gface d) ∧ q ∈ gchop1 (gface (gface d)) ∧
        q ∈ gchop1 (gface (gface (gface d))) := by
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gchop1, gchop, gtouch, halfg_gface, oddg_gface, halfg_gedge, oddg_gedge,
      arcg, ccw, hx, hy] <;> omega

/-- Shifting a dart around the edge it shares with the next pixel leaves its
half-plane unchanged. -/
theorem gchop_shift (d : GPoint) : gchop (gface (gedge (gface d))) = gchop d := by
  ext q
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gchop, halfg_gface, oddg_gface, halfg_gedge, oddg_gedge, arcg, ccw, hx, hy]

/-- The wide half-plane is likewise invariant under that shift. -/
theorem gchop1_shift (d : GPoint) : gchop1 (gface (gedge (gface d))) = gchop1 d := by
  ext q
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gchop1, gchop, halfg_gface, oddg_gface, halfg_gedge, oddg_gedge, arcg, ccw,
      hx, hy]

/-- The last dart of the opposite pixel has the wide half-plane of the second
dart. -/
theorem gchop1_gface3_gedge (d : GPoint) :
    gchop1 (gface (gface (gface (gedge d)))) = gchop1 (gface d) := by
  ext q
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gchop1, gchop, halfg_gface, oddg_gface, halfg_gedge, oddg_gedge, arcg, ccw,
      hx, hy]

/-- The pixel across an edge touches the pixel of the dart. -/
theorem gtouch_gedge (d : GPoint) : halfg (gedge d) ∈ (gtouch (halfg d)).toRegion := by
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gtouch, halfg_gedge, arcg, ccw, hx, hy] <;> omega

/-- The inset is contained in the rectangle. -/
theorem GRect.mem_of_mem_inset {r : GRect} {p : GPoint} (h : p ∈ r.inset.toRegion) :
    p ∈ r.toRegion := by
  simp only [GRect.inset, GRect.mem_toRegion] at h ⊢
  omega

/-- If the pixel across the edge of `d` lies in `r` and the chopped rectangle is
nonempty, then the pixel of `d` lies in the chopped rectangle. -/
theorem mem_gchopRect_halfg {r : GRect} {d q : GPoint}
    (he : halfg (gedge d) ∈ r.toRegion) (hq : q ∈ (gchopRect r d).toRegion) :
    halfg d ∈ (gchopRect r d).toRegion := by
  rw [mem_gchopRect] at hq ⊢
  refine ⟨?_, gchop_halfg d⟩
  obtain ⟨hqr, hqc⟩ := hq
  revert he hqr hqc
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [GRect.mem_toRegion, gchop, halfg_gedge, arcg, ccw, hx, hy] <;> omega

/-- If the pixel of `d` is inset in `r` and the pixel two steps across the edge
of `d` still lies in `r`, then the pixel across the edge of `d` is inset too. -/
theorem mem_inset_gedge {r : GRect} {d : GPoint} (hp : halfg d ∈ r.inset.toRegion)
    (h2 : halfg (gedge (gface (gface (gedge d)))) ∈ r.toRegion) :
    halfg (gedge d) ∈ r.inset.toRegion := by
  revert hp h2
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [GRect.inset, GRect.mem_toRegion, halfg_gedge, halfg_gface, oddg_gface,
      oddg_gedge, arcg, ccw, hx, hy] <;> omega

theorem gnode_gnode_eq (p : GPoint) :
    gnode (gnode p) = p - arcg (oddg p) - arcg (ccw (oddg p)) := by
  rw [gnode_def (gnode p), oddg_gnode, gnode_def p]

/-- The second node neighbour of a pixel still touches it. -/
theorem gnode_gnode_mem_gtouch (p : GPoint) :
    gnode (gnode p) ∈ (gtouch p).toRegion := by
  rw [gnode_gnode_eq]
  rcases oddgP p with ⟨hx | hx, hy | hy⟩ <;>
    simp [gtouch, arcg, ccw, hx, hy] <;> omega

/-- A rectangle containing a pixel and its second node neighbour contains the
first one. -/
theorem mem_of_gnode_gnode {r : GRect} {p : GPoint} (h1 : p ∈ r.toRegion)
    (h2 : gnode (gnode p) ∈ r.toRegion) : gnode p ∈ r.toRegion := by
  rw [gnode_gnode_eq] at h2
  rw [gnode_def]
  revert h1 h2
  rcases oddgP p with ⟨hx | hx, hy | hy⟩ <;>
    simp [GRect.mem_toRegion, arcg, ccw, hx, hy] <;> omega

end FourColor

import FourColor.Matte
import FourColor.RealPlane

/-!
# Approximating the real plane by the grid

Approximations of real scalars, points, regions and rectangles, used to cast the
continuous four colour problem into a combinatorial one.  Because the grid
decomposition proceeds by dichotomy, real coordinates are approximated by binary
fractions `m / 2 ^ s` rather than by arbitrary rationals.

The reference carries its own axiomatisation of the reals, so it must first
build powers of two, their order properties and the archimedean property.  Here
the reals are Mathlib's `ℝ`: `exp2R s` is `(2 : ℝ) ^ s`, `scale s m` is
`m / 2 ^ s`, and `approx s x m` says exactly that `m = ⌊2 ^ s * x⌋`, so
existence and uniqueness of approximations are `Int.floor` lemmas and the
scaling lemma `exists_exp2_mul_gt` is archimedeanity.

## Main definitions

* `Approx s x m` — `m` is the integer approximation of `x : ℝ` at scale `s`,
  that is `m ≤ 2 ^ s * x < m + 1`; `gapprox s z` is the approximating grid point
  of `z : Point`, and `ApproxPoint s z p` says `p` is that point.
* `scaleR s m`, `scalePoint s p` — the inverse operation, scaling an integer or
  a grid point back down by `2 ^ s`.
* `memApprox s gr` — the region of points whose approximation at scale `s` lies
  in the set `gr` of grid pixels.
* `SRect`, `SMatte` — scaled grid rectangles and mattes, with their regions
  `SRect.toRegion`, `SMatte.toRegion`, refinements `refineSRect`,
  `refineSMatte`, and the inset `SRect.inset`.
* `Rect.cap` — the intersection of two rectangles.
* `sepInterval`, `sepRect` — an interval, resp. rectangle, containing the second
  argument but not the first, unless the two are equal.

## Main results

* `approx_rect` — every point of an open rectangle lies in the inset of a scaled
  grid rectangle whose region is contained in that rectangle.
* `rect_approx` — conversely, the region of `ltouch p` is a rectangle
  neighbourhood of every point that `p` approximates.
* `toRegion_refineSRect`, `toRegion_refineSMatte` — refining a scaled rectangle
  or matte does not change its region; `inset_refineSRect` — a point inset in a
  scaled rectangle stays inset in its refinements.
* `meet_sepRect` — a point meeting both separating rectangles of `z₁` and `z₂`
  forces `z₁ = z₂`.

## References

Gonthier's `theories/proof/approx.v`.
-/

namespace FourColor

/-! ### Powers of two -/

/-- The scale factor `2 ^ s` is positive. -/
theorem exp2_pos (s : ℕ) : (0 : ℝ) < 2 ^ s := by positivity

/-- Scaling by a larger power of two only increases a positive quantity. -/
theorem one_lt_exp2_mul_of_le {s t : ℕ} {d : ℝ} (hd : 0 < d) (hst : s ≤ t)
    (h : 1 < 2 ^ s * d) : 1 < 2 ^ t * d :=
  h.trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hst) hd.le)

/-- Archimedeanity, in the form used for approximations: any positive real can
be scaled past `1` by a power of two. -/
theorem exists_exp2_mul_gt {x : ℝ} (hx : 0 < x) : ∃ s : ℕ, 1 < 2 ^ s * x := by
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (1 / x) (one_lt_two (α := ℝ))
  exact ⟨s, (div_lt_iff₀ hx).mp hs⟩

/-! ### Approximation of a real number -/

/-- `Approx s x m` states that the integer `m` approximates `x` at scale `s`,
that is, `m ≤ 2 ^ s * x < m + 1`. -/
def Approx (s : ℕ) (x : ℝ) (m : ℤ) : Prop :=
  (m : ℝ) ≤ 2 ^ s * x ∧ 2 ^ s * x < m + 1

/-- The approximation of `x` at scale `s` is the floor of `2 ^ s * x`. -/
theorem approx_iff {s : ℕ} {x : ℝ} {m : ℤ} : Approx s x m ↔ ⌊(2 : ℝ) ^ s * x⌋ = m :=
  Int.floor_eq_iff.symm

/-- The floor is an approximation. -/
theorem approx_floor (s : ℕ) (x : ℝ) : Approx s x ⌊(2 : ℝ) ^ s * x⌋ := approx_iff.mpr rfl

/-- Approximations at a given scale are unique. -/
theorem approx_inj {s : ℕ} {x : ℝ} {m₁ m₂ : ℤ} (h₁ : Approx s x m₁) (h₂ : Approx s x m₂) :
    m₁ = m₂ :=
  (approx_iff.mp h₁).symm.trans (approx_iff.mp h₂)

/-- Approximations exist at every scale. -/
theorem approx_exists (s : ℕ) (x : ℝ) : ∃ m : ℤ, Approx s x m := ⟨_, approx_floor s x⟩

/-- An integer scaled back by `s`: the binary fraction `m / 2 ^ s`. -/
noncomputable def scaleR (s : ℕ) (m : ℤ) : ℝ := (m : ℝ) / 2 ^ s

/-- A binary fraction is approximated by its numerator. -/
theorem approx_scaleR (s : ℕ) (m : ℤ) : Approx s (scaleR s m) m := by
  have h : (2 : ℝ) ^ s * scaleR s m = (m : ℝ) := by
    rw [scaleR, mul_div_cancel₀ _ (exp2_pos s).ne']
  exact ⟨h.ge, by rw [h]; linarith⟩

/-- Halving an approximation lowers its scale: this is the arithmetic behind
`halfg`. -/
theorem approx_half {s : ℕ} {x : ℝ} {m : ℤ} (h : Approx (s + 1) x m) : Approx s x (m / 2) := by
  obtain ⟨h₁, h₂⟩ := h
  have hq : 2 * (m / 2) + m % 2 = m := by omega
  have hr : 0 ≤ m % 2 ∧ m % 2 ≤ 1 := by omega
  have hqR : 2 * ((m / 2 : ℤ) : ℝ) + ((m % 2 : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast hq
  have hr0 : (0 : ℝ) ≤ ((m % 2 : ℤ) : ℝ) := by exact_mod_cast hr.1
  have hr1 : ((m % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hr.2
  have hp : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  rw [hp] at h₁ h₂
  exact ⟨by linarith, by linarith⟩

/-- If two approximations at scale `s + 1` are separated by more than one unit
at scale `s`, there is an integer strictly between them, with room to spare. -/
theorem approx_between {s : ℕ} {x₁ x₂ : ℝ} {m₁ m₂ : ℤ} (h₁ : Approx (s + 1) x₁ m₁)
    (h₂ : Approx (s + 1) x₂ m₂) (hd : 1 < 2 ^ s * (x₂ - x₁)) :
    ∃ m : ℤ, m₁ + 1 ≤ m ∧ m + 1 ≤ m₂ := by
  obtain ⟨ha, hb⟩ := approx_floor s (x₁ + x₂)
  set m := ⌊(2 : ℝ) ^ s * (x₁ + x₂)⌋ with hm
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  have hp : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  rw [hp] at h₁a h₁b h₂a h₂b
  have hy : (2 : ℝ) ^ s * (x₁ + x₂) = 2 ^ s * x₁ + 2 ^ s * x₂ := by ring
  have hz : (2 : ℝ) ^ s * (x₂ - x₁) = 2 ^ s * x₂ - 2 ^ s * x₁ := by ring
  rw [hy] at ha hb
  rw [hz] at hd
  refine ⟨m, ?_, ?_⟩
  · have hlt : (m₁ : ℝ) < (m : ℝ) := by linarith
    have : m₁ < m := by exact_mod_cast hlt
    omega
  · have hlt : ((m : ℤ) : ℝ) < (m₂ : ℝ) := by linarith
    have : m < m₂ := by exact_mod_cast hlt
    omega

/-- Approximations at the same scale are ordered by their reals: an integer gap
of one unit separates the reals strictly. -/
theorem lt_of_approx {s : ℕ} {u v : ℝ} {mu mv : ℤ} (hu : Approx s u mu) (hv : Approx s v mv)
    (h : mu + 1 ≤ mv) : u < v := by
  have h₃ : ((mu : ℝ) + 1) ≤ (mv : ℝ) := by exact_mod_cast h
  have h₄ : (2 : ℝ) ^ s * u < 2 ^ s * v := by linarith [hu.2, hv.1]
  exact lt_of_mul_lt_mul_left h₄ (exp2_pos s).le

/-- A real within one unit of `m` at scale `s` is approximated by `m - 1` or by
`m`. -/
theorem approx_near {s : ℕ} {x : ℝ} {m n : ℤ} (hn : Approx s x n)
    (h₁ : (m : ℝ) - 1 < 2 ^ s * x) (h₂ : 2 ^ s * x < (m : ℝ) + 1) :
    m - 1 ≤ n ∧ n < m + 1 := by
  obtain ⟨ha, hb⟩ := hn
  constructor
  · have h : (m : ℝ) < (n : ℝ) + 2 := by linarith
    have : m < n + 2 := by exact_mod_cast h
    omega
  · have h : (n : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt ha h₂
    exact_mod_cast h

/-! ### Approximation of a point -/

/-- The grid point approximating `z` at scale `s`. -/
noncomputable def gapprox (s : ℕ) (z : Point) : GPoint :=
  (⌊(2 : ℝ) ^ s * z.1⌋, ⌊(2 : ℝ) ^ s * z.2⌋)

/-- `ApproxPoint s z p` states that the grid point `p` approximates the point
`z` at scale `s`, coordinatewise. -/
def ApproxPoint (s : ℕ) (z : Point) (p : GPoint) : Prop :=
  Approx s z.1 p.1 ∧ Approx s z.2 p.2

/-- `gapprox s z` approximates `z`. -/
theorem approxPoint_gapprox (s : ℕ) (z : Point) : ApproxPoint s z (gapprox s z) :=
  ⟨approx_floor s z.1, approx_floor s z.2⟩

/-- The approximation of a point is `gapprox`. -/
theorem approxPoint_eq {s : ℕ} {z : Point} {p : GPoint} (h : ApproxPoint s z p) :
    p = gapprox s z :=
  Prod.ext (approx_iff.mp h.1).symm (approx_iff.mp h.2).symm

/-- Point approximations at a given scale are unique. -/
theorem approxPoint_inj {s : ℕ} {z : Point} {p₁ p₂ : GPoint} (h₁ : ApproxPoint s z p₁)
    (h₂ : ApproxPoint s z p₂) : p₁ = p₂ :=
  (approxPoint_eq h₁).trans (approxPoint_eq h₂).symm

/-- Point approximations exist at every scale. -/
theorem approxPoint_exists (s : ℕ) (z : Point) : ∃ p : GPoint, ApproxPoint s z p :=
  ⟨_, approxPoint_gapprox s z⟩

/-- A grid point scaled back by `s`. -/
noncomputable def scalePoint (s : ℕ) (p : GPoint) : Point := (scaleR s p.1, scaleR s p.2)

/-- A scaled grid point is approximated by the point it came from. -/
theorem approxPoint_scalePoint (s : ℕ) (p : GPoint) : ApproxPoint s (scalePoint s p) p :=
  ⟨approx_scaleR s p.1, approx_scaleR s p.2⟩

/-- Halving a point approximation lowers its scale, taking `halfg`. -/
theorem approxPoint_halfg {s : ℕ} {z : Point} {p : GPoint} (h : ApproxPoint (s + 1) z p) :
    ApproxPoint s z (halfg p) :=
  ⟨approx_half h.1, approx_half h.2⟩

/-! ### Approximated regions -/

/-- The region of points whose approximation at scale `s` lies in the set of
pixels `gr`. -/
def memApprox (s : ℕ) (gr : Set GPoint) : Region := {z | ∃ p, ApproxPoint s z p ∧ p ∈ gr}

/-- `memApprox` is monotone in the set of pixels. -/
theorem memApprox_mono {s : ℕ} {gr₁ gr₂ : Set GPoint} (h : gr₁ ⊆ gr₂) :
    memApprox s gr₁ ⊆ memApprox s gr₂ := fun _ ⟨p, hp, hg⟩ => ⟨p, hp, h hg⟩

/-- A scaled grid point lies in the approximated region exactly when the grid
point lies in the pixel set. -/
theorem memApprox_scalePoint {s : ℕ} {gr : Set GPoint} {p : GPoint} :
    scalePoint s p ∈ memApprox s gr ↔ p ∈ gr := by
  constructor
  · rintro ⟨q, hq, hg⟩
    rwa [approxPoint_inj (approxPoint_scalePoint s p) hq]
  · exact fun h => ⟨p, approxPoint_scalePoint s p, h⟩

/-- The pixels of a refined rectangle are the pixels whose halves lie in the
original one. -/
theorem toRegion_refineRect (r : GRect) : (refineRect r).toRegion = halfg ⁻¹' r.toRegion := by
  ext p
  exact mem_refineRect r p

/-- Refining the grid does not change the approximated region. -/
theorem memApprox_refine (s : ℕ) (gr : Set GPoint) :
    memApprox (s + 1) (halfg ⁻¹' gr) = memApprox s gr := by
  ext z
  constructor
  · rintro ⟨p, hp, hg⟩
    exact ⟨halfg p, approxPoint_halfg hp, hg⟩
  · rintro ⟨p, hp, hg⟩
    refine ⟨gapprox (s + 1) z, approxPoint_gapprox _ _, ?_⟩
    have hh : halfg (gapprox (s + 1) z) = p :=
      approxPoint_inj (approxPoint_halfg (approxPoint_gapprox (s + 1) z)) hp
    rw [Set.mem_preimage, hh]
    exact hg

/-- A point inset in a rectangle is still inset in its refinement. -/
theorem memApprox_refine_inset (s : ℕ) (b : GRect) :
    memApprox s b.inset.toRegion ⊆ memApprox (s + 1) (refineRect b).inset.toRegion := by
  intro z hz
  rw [← memApprox_refine s b.inset.toRegion] at hz
  obtain ⟨p, hp, hg⟩ := hz
  refine ⟨p, hp, GRect.mem_of_mem_inset ?_⟩
  have : p ∈ (refineRect b.inset).toRegion := (mem_refineRect _ p).mpr hg
  rwa [refine_inset] at this

/-- Iterated refinement does not change the approximated region of a
rectangle. -/
theorem memApprox_iterate_refineRect (s : ℕ) : ∀ (t : ℕ) (r : GRect),
    memApprox (t + s) (refineRect^[s] r).toRegion = memApprox t r.toRegion := by
  induction s with
  | zero => intro t r; rfl
  | succ s ih =>
    intro t r
    rw [Function.iterate_succ_apply, show t + (s + 1) = t + 1 + s by omega,
      ih (t + 1) (refineRect r), toRegion_refineRect, memApprox_refine]

/-- A point inset in a rectangle stays inset in all its refinements. -/
theorem memApprox_iterate_refine_inset (s : ℕ) : ∀ (t : ℕ) (r : GRect),
    memApprox t r.inset.toRegion ⊆ memApprox (t + s) (refineRect^[s] r).inset.toRegion := by
  induction s with
  | zero => intro t r; exact fun _ hz => hz
  | succ s ih =>
    intro t r z hz
    rw [Function.iterate_succ_apply, show t + (s + 1) = t + 1 + s by omega]
    exact ih (t + 1) (refineRect r) (memApprox_refine_inset t r hz)

/-! ### Scaled rectangles -/

/-- A grid rectangle together with the scale at which it is read. -/
structure SRect where
  /-- The scale. -/
  scale : ℕ
  /-- The grid rectangle. -/
  rect : GRect

/-- The region of the plane a scaled rectangle denotes. -/
def SRect.toRegion (b : SRect) : Region := memApprox b.scale b.rect.toRegion

/-- The scaled rectangle inset by one pixel; this insets the corresponding real
region by `1 / 2 ^ s` on all sides. -/
def SRect.inset (b : SRect) : SRect := ⟨b.scale, b.rect.inset⟩

/-- The scaled rectangle obtained by increasing the scale by `s` while scaling
the coordinates up by the same amount. -/
def refineSRect (s : ℕ) (b : SRect) : SRect := ⟨b.scale + s, refineRect^[s] b.rect⟩

/-- Refining a scaled rectangle does not change its region. -/
theorem toRegion_refineSRect (s : ℕ) (b : SRect) : (refineSRect s b).toRegion = b.toRegion :=
  memApprox_iterate_refineRect s b.scale b.rect

/-- A point inset in a scaled rectangle stays inset in its refinements. -/
theorem inset_refineSRect (s : ℕ) (b : SRect) :
    b.inset.toRegion ⊆ (refineSRect s b).inset.toRegion :=
  memApprox_iterate_refine_inset s b.scale b.rect

/-! ### Rectangles and their approximations -/

/-- Every point of an open rectangle is inset in a scaled grid rectangle whose
region is contained in the rectangle. -/
theorem approx_rect {z : Point} {r : Rect} (hz : z ∈ r.toRegion) :
    ∃ b : SRect, z ∈ b.inset.toRegion ∧ b.toRegion ⊆ r.toRegion := by
  obtain ⟨hx₀, hx₁, hy₀, hy₁⟩ := hz
  obtain ⟨s₁, hs₁⟩ := exists_exp2_mul_gt (sub_pos.mpr hx₀)
  obtain ⟨s₂, hs₂⟩ := exists_exp2_mul_gt (sub_pos.mpr hx₁)
  obtain ⟨s₃, hs₃⟩ := exists_exp2_mul_gt (sub_pos.mpr hy₀)
  obtain ⟨s₄, hs₄⟩ := exists_exp2_mul_gt (sub_pos.mpr hy₁)
  set s := max (max s₁ s₂) (max s₃ s₄) with hsdef
  have H₁ : 1 < 2 ^ s * (z.1 - r.x₀) :=
    one_lt_exp2_mul_of_le (sub_pos.mpr hx₀) ((le_max_left _ _).trans (le_max_left _ _)) hs₁
  have H₂ : 1 < 2 ^ s * (r.x₁ - z.1) :=
    one_lt_exp2_mul_of_le (sub_pos.mpr hx₁) ((le_max_right _ _).trans (le_max_left _ _)) hs₂
  have H₃ : 1 < 2 ^ s * (z.2 - r.y₀) :=
    one_lt_exp2_mul_of_le (sub_pos.mpr hy₀) ((le_max_left _ _).trans (le_max_right _ _)) hs₃
  have H₄ : 1 < 2 ^ s * (r.y₁ - z.2) :=
    one_lt_exp2_mul_of_le (sub_pos.mpr hy₁) ((le_max_right _ _).trans (le_max_right _ _)) hs₄
  have Dx : Approx (s + 1) z.1 ⌊(2 : ℝ) ^ (s + 1) * z.1⌋ := approx_floor _ _
  have Dy : Approx (s + 1) z.2 ⌊(2 : ℝ) ^ (s + 1) * z.2⌋ := approx_floor _ _
  have Dx₀ : Approx (s + 1) r.x₀ ⌊(2 : ℝ) ^ (s + 1) * r.x₀⌋ := approx_floor _ _
  have Dx₁ : Approx (s + 1) r.x₁ ⌊(2 : ℝ) ^ (s + 1) * r.x₁⌋ := approx_floor _ _
  have Dy₀ : Approx (s + 1) r.y₀ ⌊(2 : ℝ) ^ (s + 1) * r.y₀⌋ := approx_floor _ _
  have Dy₁ : Approx (s + 1) r.y₁ ⌊(2 : ℝ) ^ (s + 1) * r.y₁⌋ := approx_floor _ _
  obtain ⟨nx₀, hnx₀, hnx₀'⟩ := approx_between Dx₀ Dx H₁
  obtain ⟨nx₁, hnx₁, hnx₁'⟩ := approx_between Dx Dx₁ H₂
  obtain ⟨ny₀, hny₀, hny₀'⟩ := approx_between Dy₀ Dy H₃
  obtain ⟨ny₁, hny₁, hny₁'⟩ := approx_between Dy Dy₁ H₄
  refine ⟨⟨s + 1, ⟨nx₀, nx₁ + 1, ny₀, ny₁ + 1⟩⟩, ⟨gapprox (s + 1) z, approxPoint_gapprox _ _, ?_⟩,
    ?_⟩
  · simp only [SRect.inset, GRect.inset, GRect.mem_toRegion, gapprox]
    omega
  · rintro w ⟨q, hq, hqm⟩
    simp only [GRect.mem_toRegion] at hqm
    obtain ⟨hq₁, hq₂, hq₃, hq₄⟩ := hqm
    refine ⟨lt_of_approx Dx₀ hq.1 (by omega), lt_of_approx hq.1 Dx₁ (by omega),
      lt_of_approx Dy₀ hq.2 (by omega), lt_of_approx hq.2 Dy₁ (by omega)⟩

/-- The region of the four pixels around a grid point is a neighbourhood of any
point that grid point approximates. -/
theorem rect_approx {s : ℕ} {z : Point} {p : GPoint} (h : ApproxPoint s z p) :
    ∃ r : Rect, z ∈ r.toRegion ∧ r.toRegion ⊆ memApprox s (ltouch p).toRegion := by
  have hpos := exp2_pos s
  refine ⟨⟨scaleR s (p.1 - 1), scaleR s (p.1 + 1), scaleR s (p.2 - 1), scaleR s (p.2 + 1)⟩,
    ?_, ?_⟩
  · obtain ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [scaleR, Int.cast_sub, Int.cast_add, Int.cast_one, div_lt_iff₀ hpos,
        lt_div_iff₀ hpos] <;> nlinarith
  · rintro w ⟨hw₁, hw₂, hw₃, hw₄⟩
    simp only [scaleR, Int.cast_sub, Int.cast_add, Int.cast_one, div_lt_iff₀ hpos,
      lt_div_iff₀ hpos] at hw₁ hw₂ hw₃ hw₄
    refine ⟨gapprox s w, approxPoint_gapprox s w, ?_⟩
    have hx := approx_near (m := p.1) (approx_floor s w.1) (by linarith) (by linarith)
    have hy := approx_near (m := p.2) (approx_floor s w.2) (by linarith) (by linarith)
    simp only [ltouch, GRect.mem_toRegion, gapprox]
    omega

/-! ### Intersecting and separating rectangles -/

/-- The intersection of two rectangles. -/
noncomputable def Rect.cap (r₁ r₂ : Rect) : Rect :=
  ⟨max r₁.x₀ r₂.x₀, min r₁.x₁ r₂.x₁, max r₁.y₀ r₂.y₀, min r₁.y₁ r₂.y₁⟩

/-- The region of the intersection is the intersection of the regions. -/
theorem Rect.cap_toRegion (r₁ r₂ : Rect) :
    (r₁.cap r₂).toRegion = r₁.toRegion ∩ r₂.toRegion := by
  ext z
  simp only [Rect.cap, Rect.toRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, max_lt_iff,
    lt_min_iff]
  tauto

/-- A point lies in the intersection rectangle exactly when it lies in both. -/
theorem Rect.mem_cap (r₁ r₂ : Rect) (z : Point) :
    z ∈ (r₁.cap r₂).toRegion ↔ z ∈ r₁.toRegion ∧ z ∈ r₂.toRegion := by
  rw [Rect.cap_toRegion, Set.mem_inter_iff]

/-- The lower bound of the interval separating `x₂` from `x₁`. -/
noncomputable def sepLo (x₁ x₂ : ℝ) : ℝ := if x₂ ≤ (x₁ + x₂) / 2 then x₂ - 1 else (x₁ + x₂) / 2

/-- The upper bound of the interval separating `x₂` from `x₁`. -/
noncomputable def sepHi (x₁ x₂ : ℝ) : ℝ := if (x₁ + x₂) / 2 ≤ x₂ then x₂ + 1 else (x₁ + x₂) / 2

/-- An open interval containing `x₂`, and containing `x₁` only if `x₁ = x₂`. -/
noncomputable def sepInterval (x₁ x₂ : ℝ) : Set ℝ := Set.Ioo (sepLo x₁ x₂) (sepHi x₁ x₂)

/-- The separating interval of `x₂` contains `x₂`. -/
theorem mem_sepInterval (x₁ x₂ : ℝ) : x₂ ∈ sepInterval x₁ x₂ := by
  constructor
  · simp only [sepLo]
    split_ifs with hc
    · linarith
    · exact lt_of_not_ge hc
  · simp only [sepHi]
    split_ifs with hc
    · linarith
    · exact lt_of_not_ge hc

/-- Two separating intervals meet only if the two points coincide. -/
theorem meet_sepInterval {x y t : ℝ} (h₁ : t ∈ sepInterval x y) (h₂ : t ∈ sepInterval y x) :
    x = y := by
  obtain ⟨h₁lo, h₁hi⟩ := h₁
  obtain ⟨h₂lo, h₂hi⟩ := h₂
  simp only [sepLo, sepHi] at h₁lo h₁hi h₂lo h₂hi
  split_ifs at h₁lo h₁hi h₂lo h₂hi <;> linarith

/-- A rectangle containing `z₂`, and containing `z₁` only if `z₁ = z₂`. -/
noncomputable def sepRect (z₁ z₂ : Point) : Rect :=
  ⟨sepLo z₁.1 z₂.1, sepHi z₁.1 z₂.1, sepLo z₁.2 z₂.2, sepHi z₁.2 z₂.2⟩

/-- The separating rectangle of `z₂` contains `z₂`. -/
theorem mem_sepRect (z₁ z₂ : Point) : z₂ ∈ (sepRect z₁ z₂).toRegion :=
  ⟨(mem_sepInterval z₁.1 z₂.1).1, (mem_sepInterval z₁.1 z₂.1).2,
    (mem_sepInterval z₁.2 z₂.2).1, (mem_sepInterval z₁.2 z₂.2).2⟩

/-- Two points whose separating rectangles meet are equal.  The reference can
only conclude that the two points belong to the same regions, since its reals
are a setoid. -/
theorem meet_sepRect {z₁ z₂ : Point}
    (h : ((sepRect z₁ z₂).toRegion ∩ (sepRect z₂ z₁).toRegion).Nonempty) : z₁ = z₂ := by
  obtain ⟨w, ⟨h₁x, h₂x, h₁y, h₂y⟩, ⟨h₃x, h₄x, h₃y, h₄y⟩⟩ := h
  exact Prod.ext (meet_sepInterval ⟨h₁x, h₂x⟩ ⟨h₃x, h₄x⟩)
    (meet_sepInterval ⟨h₁y, h₂y⟩ ⟨h₃y, h₄y⟩)

/-- Consequently such points lie in exactly the same rectangles. -/
theorem meet_sepRect_mem {z₁ z₂ : Point}
    (h : ((sepRect z₁ z₂).toRegion ∩ (sepRect z₂ z₁).toRegion).Nonempty) (r : Rect)
    (hz : z₁ ∈ r.toRegion) : z₂ ∈ r.toRegion := by
  rwa [meet_sepRect h] at hz

/-! ### Scaled mattes -/

/-- A grid matte together with the scale at which it is read. -/
structure SMatte where
  /-- The scale. -/
  scale : ℕ
  /-- The grid matte. -/
  matte : Matte

/-- The (polygonal) region of the plane a scaled matte denotes. -/
def SMatte.toRegion (m : SMatte) : Region := memApprox m.scale (↑m.matte.disk : Set GPoint)

/-- The scaled matte obtained by increasing the scale by `s` while scaling the
matte up by the same amount. -/
def refineSMatte (s : ℕ) (m : SMatte) : SMatte := ⟨m.scale + s, refineMatte^[s] m.matte⟩

/-- The pixels of a refined matte are the pixels whose halves lie in the
original one. -/
theorem disk_refineMatte (m : Matte) :
    (↑(refineMatte m).disk : Set GPoint) = halfg ⁻¹' (↑m.disk : Set GPoint) := by
  ext q
  simp only [Set.mem_preimage, Finset.mem_coe, mem_refineMatte]

/-- Iterated refinement does not change the approximated region of a matte. -/
theorem memApprox_iterate_refineMatte (s : ℕ) : ∀ (t : ℕ) (m : Matte),
    memApprox (t + s) (↑(refineMatte^[s] m).disk : Set GPoint)
      = memApprox t (↑m.disk : Set GPoint) := by
  induction s with
  | zero => intro t m; rfl
  | succ s ih =>
    intro t m
    rw [Function.iterate_succ_apply, show t + (s + 1) = t + 1 + s by omega,
      ih (t + 1) (refineMatte m), disk_refineMatte, memApprox_refine]

/-- Refining a scaled matte does not change its region. -/
theorem toRegion_refineSMatte (s : ℕ) (m : SMatte) :
    (refineSMatte s m).toRegion = m.toRegion :=
  memApprox_iterate_refineMatte s m.scale m.matte

end FourColor

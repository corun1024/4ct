import FourColor.Complete
import FourColor.RealPlaneMathlib
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# The statement is not vacuous

`FourColor/RealPlane.lean` states the theorem; nothing there rules out its
being trivially true.  Two ways it could be:

* if `Adjacent` were unsatisfiable, the `Coloring.adjacent` condition would
  constrain nothing and "give every point the same colour" would prove the
  theorem;
* if `AtMostRegions n` did not really bound the number of colour classes, the
  `4` would be decorative.

This file rules both out with a witness.  Four open connected regions of the
plane — the open unit square, the strip to its right, the quadrant above, and
the complement of the closed first quadrant — form a `SimpleMap` whose four
regions are **pairwise** adjacent.  Hence `Adjacent` is satisfiable, and by
pigeonhole the map is not `ColorableWith 3`: the constant four is tight.

`applies` then instantiates `fourColorTheorem` at this map, so the theorem
demonstrably says something about a map that needs four colours.

The section `Elementary` re-proves the four closure facts behind one of the
adjacencies directly from the elementary `regionClosure`, using neither
Mathlib's `closure` nor `regionClosure_eq`, so the witness does not rest on
that bridging lemma being right.
-/

open Set

namespace FourColor.Nonvacuity
theorem isOpenRegion_rect (u : Rect) : IsOpenRegion u.toRegion :=
  fun z hz => ⟨u, hz, subset_rfl⟩

def pmap {ι : Type} (R : ι → Region) : PlaneMap := fun z => {w | ∃ i, z ∈ R i ∧ w ∈ R i}

variable {ι : Type} {R : ι → Region}

def Disj (R : ι → Region) : Prop := ∀ i j (z : Point), z ∈ R i → z ∈ R j → i = j

theorem pmap_eq (hd : Disj R) {i : ι} {z : Point} (hz : z ∈ R i) : pmap R z = R i := by
  ext w
  exact ⟨fun ⟨j, hzj, hwj⟩ => by rwa [hd j i z hzj hz] at hwj, fun hw => ⟨i, hz, hw⟩⟩

theorem pmap_empty {z : Point} (hz : ∀ i, z ∉ R i) : pmap R z = (∅ : Region) := by
  ext w; simp only [pmap, Set.mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨i, hzi, -⟩; exact hz i hzi

theorem pmap_plain (hd : Disj R) : PlainMap (pmap R) := by
  constructor
  · rintro z1 z2 ⟨i, h1, h2⟩; exact ⟨i, h2, h1⟩
  · rintro z1 z2 ⟨i, h1, h2⟩ v ⟨j, h3, h4⟩
    rw [hd j i z2 h3 h2] at h4; exact ⟨i, h1, h4⟩

theorem mem_cover_pmap {i : ι} {z : Point} (hz : z ∈ R i) : z ∈ cover (pmap R) := ⟨i, hz, hz⟩

theorem pmap_simple (hd : Disj R) (ho : ∀ i, IsOpen (R i)) (hc : ∀ i, IsPreconnected (R i)) :
    SimpleMap (pmap R) := by
  have key : ∀ z : Point, (∃ i, z ∈ R i ∧ pmap R z = R i) ∨ pmap R z = (∅ : Region) := by
    intro z
    by_cases h : ∃ i, z ∈ R i
    · obtain ⟨i, hi⟩ := h; exact Or.inl ⟨i, hi, pmap_eq hd hi⟩
    · exact Or.inr (pmap_empty (by push_neg at h; exact h))
  refine ⟨pmap_plain hd, fun z => ?_, fun z => ?_⟩
  · rcases key z with ⟨i, -, he⟩ | he
    · rw [he]; exact (isOpenRegion_iff _).mpr (ho i)
    · rw [he]; exact (isOpenRegion_iff _).mpr isOpen_empty
  · rcases key z with ⟨i, -, he⟩ | he
    · rw [he]; exact isConnectedRegion_of_isPreconnected (hc i)
    · rw [he]; exact isConnectedRegion_of_isPreconnected isPreconnected_empty

/-- The key adjacency lemma for a partition map. -/
theorem adjacent_pmap (hd : Disj R) {i j : ι} (hij : i ≠ j) {zi zj : Point}
    (hzi : zi ∈ R i) (hzj : zj ∈ R j) (b : Point)
    (hbi : b ∈ regionClosure (R i)) (hbj : b ∈ regionClosure (R j))
    (hother : ∀ l, b ∈ regionClosure (R l) → l = i ∨ l = j) :
    Adjacent (pmap R) zi zj := by
  constructor
  · rw [pmap_eq hd hzi]; exact fun h => hij (hd i j zj h hzj)
  · refine ⟨b, ?_, ?_⟩
    · -- b is a non-corner point: only regions i and j have b in their closure
      refine ⟨fun n => if n = 0 then zi else zj, ?_⟩
      rintro z' ⟨⟨l, hzl, -⟩, hbcl⟩
      rw [pmap_eq hd hzl] at hbcl
      rcases hother l hbcl with rfl | rfl
      · exact ⟨0, by norm_num, by simpa [cornerMap, pmap_eq hd hzi] using ⟨hzl, hbi⟩⟩
      · exact ⟨1, by norm_num, by simpa [cornerMap, pmap_eq hd hzj] using ⟨hzl, hbj⟩⟩
    · exact ⟨by rw [pmap_eq hd hzi]; exact hbi, by rw [pmap_eq hd hzj]; exact hbj⟩

/-- Pigeonhole: `n+1` pairwise adjacent regions cannot be coloured with `n` colours. -/
theorem not_colorable {m : PlaneMap} {n : ℕ} (p : Fin (n+1) → Point)
    (hcov : ∀ a, p a ∈ cover m)
    (hadj : ∀ a b, a ≠ b → Adjacent m (p a) (p b)) : ¬ ColorableWith n m := by
  rintro ⟨k, hk, f, hf⟩
  have hck : ∀ a, p a ∈ cover k := fun a => hk.consistent (p a) (hcov a)
  choose g hg hgm using fun a => hf (p a) (hck a)
  obtain ⟨a, b, hab, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun a : Fin (n+1) => (⟨g a, hg a⟩ : Fin n)) (by simp)
  have hge : g a = g b := congrArg Fin.val heq
  have h1 : p a ∈ k (f (g a)) := hgm a
  have h2 : p b ∈ k (f (g a)) := hge ▸ hgm b
  exact (hk.adjacent (p a) (p b) (hadj a b hab)) (hk.plain.trans _ _ (hk.plain.symm _ _ h1) h2)


/-! ## A concrete K4 map of the real plane

Four open, connected, pairwise disjoint regions, pairwise adjacent:
* `A` the open unit square,
* `B` the strip `x > 1, 0 < y < 1`,
* `C` the quadrant `x > 0, y > 1`,
* `D` the complement of the closed first quadrant.
-/

def RA : Region := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1
def RB : Region := Ioi (1:ℝ) ×ˢ Ioo (0:ℝ) 1
def RC : Region := Ioi (0:ℝ) ×ˢ Ioi (1:ℝ)
def RD : Region := (Iio (0:ℝ) ×ˢ (univ : Set ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iio (0:ℝ))

def RR : Fin 4 → Region
  | 0 => RA | 1 => RB | 2 => RC | 3 => RD

def M : PlaneMap := pmap RR

theorem clA : closure RA = Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  rw [RA, closure_prod_eq]; simp
theorem clB : closure RB = Ici (1:ℝ) ×ˢ Icc (0:ℝ) 1 := by
  rw [RB, closure_prod_eq]; simp
theorem clC : closure RC = Ici (0:ℝ) ×ˢ Ici (1:ℝ) := by
  rw [RC, closure_prod_eq]; simp
theorem clD : closure RD = (Iic (0:ℝ) ×ˢ (univ : Set ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0:ℝ)) := by
  rw [RD, closure_union, closure_prod_eq, closure_prod_eq]; simp

theorem RR0 : RR 0 = RA := rfl
theorem RR1 : RR 1 = RB := rfl
theorem RR2 : RR 2 = RC := rfl
theorem RR3 : RR 3 = RD := rfl

theorem fin4 : ∀ l : Fin 4, l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by decide

theorem rc0 : regionClosure (RR 0) = Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
  rw [regionClosure_eq, RR0]; exact clA
theorem rc1 : regionClosure (RR 1) = Ici (1:ℝ) ×ˢ Icc (0:ℝ) 1 := by
  rw [regionClosure_eq, RR1]; exact clB
theorem rc2 : regionClosure (RR 2) = Ici (0:ℝ) ×ˢ Ici (1:ℝ) := by
  rw [regionClosure_eq, RR2]; exact clC
theorem rc3 : regionClosure (RR 3) =
    (Iic (0:ℝ) ×ˢ (univ : Set ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0:ℝ)) := by
  rw [regionClosure_eq, RR3]; exact clD

theorem disjRR : Disj RR := by
  intro i j z hi hj
  rcases fin4 i with rfl|rfl|rfl|rfl <;> rcases fin4 j with rfl|rfl|rfl|rfl <;>
    simp_all [RR0, RR1, RR2, RR3, RA, RB, RC, RD, mem_prod, mem_Ioo, mem_Ioi, mem_Iio] <;>
    (try rcases hi with h | h) <;> (try rcases hj with h | h) <;> linarith

theorem openRR : ∀ l, IsOpen (RR l) := by
  intro l; rcases fin4 l with rfl|rfl|rfl|rfl
  · rw [RR0, RA]; exact isOpen_Ioo.prod isOpen_Ioo
  · rw [RR1, RB]; exact isOpen_Ioi.prod isOpen_Ioo
  · rw [RR2, RC]; exact isOpen_Ioi.prod isOpen_Ioi
  · rw [RR3, RD]; exact (isOpen_Iio.prod isOpen_univ).union (isOpen_univ.prod isOpen_Iio)

theorem connRR : ∀ l, IsPreconnected (RR l) := by
  intro l; rcases fin4 l with rfl|rfl|rfl|rfl
  · rw [RR0, RA]; exact ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
  · rw [RR1, RB]; exact ((convex_Ioi _).prod (convex_Ioo _ _)).isPreconnected
  · rw [RR2, RC]; exact ((convex_Ioi _).prod (convex_Ioi _)).isPreconnected
  · rw [RR3, RD]
    refine IsPreconnected.union ((-1 : ℝ), (-1 : ℝ)) ⟨by norm_num, trivial⟩ ⟨trivial, by norm_num⟩
      (((convex_Iio _).prod convex_univ).isPreconnected)
      (((convex_univ).prod (convex_Iio _)).isPreconnected)

theorem simpleM : SimpleMap M := pmap_simple disjRR openRR connRR


/-! ### The six adjacencies -/

theorem adjacent_symm {m : PlaneMap} (hp : PlainMap m) {z1 z2 : Point}
    (h : Adjacent m z1 z2) : Adjacent m z2 z1 := by
  refine ⟨fun hc => h.1 (hp.symm _ _ hc), ?_⟩
  obtain ⟨b, hb, hb1, hb2⟩ := h.2
  exact ⟨b, hb, hb2, hb1⟩

noncomputable def pA : Point := (1/2, 1/2)
noncomputable def pB : Point := (2, 1/2)
noncomputable def pC : Point := (1/2, 2)
noncomputable def pD : Point := (-1, -1)

theorem mA : pA ∈ RR 0 := by rw [RR0, RA]; norm_num [pA, mem_prod]
theorem mB : pB ∈ RR 1 := by rw [RR1, RB]; norm_num [pB, mem_prod]
theorem mC : pC ∈ RR 2 := by rw [RR2, RC]; norm_num [pC, mem_prod]
theorem mD : pD ∈ RR 3 := by rw [RR3, RD]; norm_num [pD, mem_prod]

/-- Border points. -/
noncomputable def bAB : Point := (1, 1/2)
noncomputable def bAC : Point := (1/2, 1)
noncomputable def bBC : Point := (2, 1)
noncomputable def bAD : Point := (0, 1/2)
noncomputable def bBD : Point := (2, 0)
noncomputable def bCD : Point := (0, 2)

theorem adjAB : Adjacent M pA pB := by
  refine adjacent_pmap disjRR (by decide) mA mB bAB ?_ ?_ ?_
  · rw [rc0]; norm_num [bAB, mem_prod]
  · rw [rc1]; norm_num [bAB, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [rc2] at h; exfalso; norm_num [bAB, mem_prod] at h
    · rw [rc3] at h; exfalso; norm_num [bAB, mem_prod] at h

theorem adjAC : Adjacent M pA pC := by
  refine adjacent_pmap disjRR (by decide) mA mC bAC ?_ ?_ ?_
  · rw [rc0]; norm_num [bAC, mem_prod]
  · rw [rc2]; norm_num [bAC, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · exact Or.inl rfl
    · rw [rc1] at h; exfalso; norm_num [bAC, mem_prod] at h
    · exact Or.inr rfl
    · rw [rc3] at h; exfalso; norm_num [bAC, mem_prod] at h

theorem adjBC : Adjacent M pB pC := by
  refine adjacent_pmap disjRR (by decide) mB mC bBC ?_ ?_ ?_
  · rw [rc1]; norm_num [bBC, mem_prod]
  · rw [rc2]; norm_num [bBC, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · rw [rc0] at h; exfalso; norm_num [bBC, mem_prod] at h
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [rc3] at h; exfalso; norm_num [bBC, mem_prod] at h

theorem adjAD : Adjacent M pA pD := by
  refine adjacent_pmap disjRR (by decide) mA mD bAD ?_ ?_ ?_
  · rw [rc0]; norm_num [bAD, mem_prod]
  · rw [rc3]; norm_num [bAD, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · exact Or.inl rfl
    · rw [rc1] at h; exfalso; norm_num [bAD, mem_prod] at h
    · rw [rc2] at h; exfalso; norm_num [bAD, mem_prod] at h
    · exact Or.inr rfl

theorem adjBD : Adjacent M pB pD := by
  refine adjacent_pmap disjRR (by decide) mB mD bBD ?_ ?_ ?_
  · rw [rc1]; norm_num [bBD, mem_prod]
  · rw [rc3]; norm_num [bBD, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · rw [rc0] at h; exfalso; norm_num [bBD, mem_prod] at h
    · exact Or.inl rfl
    · rw [rc2] at h; exfalso; norm_num [bBD, mem_prod] at h
    · exact Or.inr rfl

theorem adjCD : Adjacent M pC pD := by
  refine adjacent_pmap disjRR (by decide) mC mD bCD ?_ ?_ ?_
  · rw [rc2]; norm_num [bCD, mem_prod]
  · rw [rc3]; norm_num [bCD, mem_prod]
  · intro l h; rcases fin4 l with rfl|rfl|rfl|rfl
    · rw [rc0] at h; exfalso; norm_num [bCD, mem_prod] at h
    · rw [rc1] at h; exfalso; norm_num [bCD, mem_prod] at h
    · exact Or.inl rfl
    · exact Or.inr rfl


/-! ### Consequences -/

noncomputable def P : Fin 4 → Point
  | 0 => pA | 1 => pB | 2 => pC | 3 => pD

theorem Pcov : ∀ a, P a ∈ cover M := by
  intro a; rcases fin4 a with rfl|rfl|rfl|rfl
  exacts [mem_cover_pmap mA, mem_cover_pmap mB, mem_cover_pmap mC, mem_cover_pmap mD]

theorem Padj : ∀ a b, a ≠ b → Adjacent M (P a) (P b) := by
  have sy : ∀ {z1 z2 : Point}, Adjacent M z1 z2 → Adjacent M z2 z1 :=
    fun h => adjacent_symm (pmap_plain disjRR) h
  intro a b hab
  rcases fin4 a with rfl|rfl|rfl|rfl <;> rcases fin4 b with rfl|rfl|rfl|rfl <;>
    first
      | exact absurd rfl hab
      | exact adjAB | exact adjAC | exact adjBC | exact adjAD | exact adjBD | exact adjCD
      | exact sy adjAB | exact sy adjAC | exact sy adjBC
      | exact sy adjAD | exact sy adjBD | exact sy adjCD

/-- **`Adjacent` is satisfiable**, and the map is a genuine `SimpleMap`. -/
theorem nonvacuous : ∃ m : PlaneMap, SimpleMap m ∧ ∃ z1 z2, Adjacent m z1 z2 :=
  ⟨M, simpleM, pA, pB, adjAB⟩

/-- **Four colours are necessary**: this simple map is not 3-colourable. -/
theorem notColorable3 : ¬ ColorableWith 3 M := not_colorable P Pcov Padj

/-- ... and a fortiori not 1-colourable. -/
theorem notColorable1 : ¬ ColorableWith 1 M := by
  intro ⟨k, hk, f, hf⟩
  exact notColorable3 ⟨k, hk, f, fun z hz => by
    obtain ⟨i, hi, h⟩ := hf z hz; exact ⟨i, by omega, h⟩⟩

/-- The four colour theorem does apply to this map, and gives a colouring
    that is genuinely constrained. -/
theorem applies : ColorableWith 4 M := FourColor.fourColorTheorem M simpleM
/-! ## Elementary cross-check

The adjacency of the square and the strip, re-derived at the border point
`(1, 1/2)` from the definition of `regionClosure` alone. -/

namespace Elementary
/-- Elementary: no appeal to `regionClosure_eq` or Mathlib `closure`. -/
theorem isOpenRegion_rect (u : Rect) : IsOpenRegion u.toRegion := fun z hz => ⟨u, hz, subset_rfl⟩

theorem mem_rc {r : Region} {z : Point}
    (h : ∀ u : Rect, z ∈ u.toRegion → (r ∩ u.toRegion).Nonempty) : z ∈ regionClosure r := by
  intro u hu hzu
  obtain ⟨t, hzt, htu⟩ := hu z hzu
  obtain ⟨w, hwr, hwt⟩ := h t hzt
  exact ⟨w, hwr, htu hwt⟩

theorem not_mem_rc {r : Region} {z : Point} (u : Rect)
    (hz : z ∈ u.toRegion) (hd : ∀ w ∈ u.toRegion, w ∉ r) : z ∉ regionClosure r := by
  intro h
  obtain ⟨w, hwr, hwu⟩ := h u.toRegion (isOpenRegion_rect u) hz
  exact hd w hwu hwr

def RA : Region := {z : Point | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < 1}
def RB : Region := {z : Point | 1 < z.1 ∧ 0 < z.2 ∧ z.2 < 1}
def RC : Region := {z : Point | 0 < z.1 ∧ 1 < z.2}
def RD : Region := {z : Point | z.1 < 0 ∨ z.2 < 0}

theorem e1 : ((1:ℝ), (1/2:ℝ)) ∈ regionClosure RA := by
  refine mem_rc fun u hu => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨((max u.x₀ 0 + 1)/2, 1/2), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [] <;>
    [ (have := le_max_right u.x₀ (0:ℝ); have : max u.x₀ (0:ℝ) < 1 := by
         simp only [max_lt_iff]; exact ⟨h1, by norm_num⟩); skip; skip; skip;
      (have := le_max_left u.x₀ (0:ℝ); have : max u.x₀ (0:ℝ) < 1 := by
         simp only [max_lt_iff]; exact ⟨h1, by norm_num⟩); skip; skip; skip] <;>
    first
      | linarith [le_max_left u.x₀ (0:ℝ), le_max_right u.x₀ (0:ℝ),
          (by simp only [max_lt_iff]; exact ⟨h1, by norm_num⟩ : max u.x₀ (0:ℝ) < 1)]
      | norm_num

theorem e2 : ((1:ℝ), (1/2:ℝ)) ∈ regionClosure RB := by
  refine mem_rc fun u hu => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hu
  have hb : (1:ℝ) < min u.x₁ 2 := by simp only [lt_min_iff]; exact ⟨h2, by norm_num⟩
  refine ⟨((1 + min u.x₁ 2)/2, 1/2), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [] <;>
    first
      | linarith [min_le_left u.x₁ (2:ℝ), min_le_right u.x₁ (2:ℝ), hb]
      | norm_num

theorem e3 : ((1:ℝ), (1/2:ℝ)) ∉ regionClosure RC := by
  refine not_mem_rc ⟨0, 2, 0, 1⟩ (by norm_num [Rect.toRegion]) ?_
  rintro w ⟨-, -, -, hw⟩ ⟨-, hc⟩
  simp only at hw hc; linarith

theorem e4 : ((1:ℝ), (1/2:ℝ)) ∉ regionClosure RD := by
  refine not_mem_rc ⟨0, 2, 0, 1⟩ (by norm_num [Rect.toRegion]) ?_
  rintro w ⟨hw1, -, hw3, -⟩ (hc | hc) <;> simp only at hw1 hw3 hc <;> linarith
end Elementary

end FourColor.Nonvacuity

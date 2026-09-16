import FourColor.Matte
import FourColor.Snip
import FourColor.Sew

/-!
# Grid maps: realising an abstract adjacency pattern by mattes

This file is the port of `gridmap.v`: the data describing a finite family of
grid regions together with the adjacencies we want them to realise, the theorem
that the family can always be *extended* so that every prescribed adjacency
becomes a genuine shared contour edge of two mattes, and the construction of
the *grid map*, a planar bridgeless hypermap whose four-colourings colour the
prescribed adjacency pattern.

The set-up is a number `Nr` of regions.  A family of regions is a `CMatte`, a
function `Fin Nr → Matte`; the prescribed adjacencies are recorded by an
`AdjBox`, which assigns to each ordered pair `i < j` of indices a grid
rectangle.  An improper (empty) rectangle records the absence of an adjacency;
a proper one is an *adjacency box*, a window in which the two regions are
required to meet and which no third region may enter.

The extension theorem `cm_extend_adj` is the geometric core.  Its proof first
refines the grid once, which makes every matte coarse and hence extendable by
`Matte.coarse_extends_in`, and then repeatedly applies `Matte.extend_madj`:
each application grows one matte of a still-unrealised adjacency until it
touches its partner, without ever leaving the adjacency box and without
swallowing any other matte.  The number of unrealised adjacencies strictly
decreases, which is what drives the induction.

The bounding box `cmBBox` of the extended family is the rectangle that the
remaining construction frames to obtain a plain planar connected map.

The *box map* `gmdartMap bb` lives on the `gedge`-closure of the refined
bounding box.  It is plain, connected and planar; its faces are the grid
vertices of the box and its nodes are (at least) its pixels.  Each matte
contour becomes a face-simple `Rlink` cycle of the box map bounding a disk, and
the disks of distinct mattes are disjoint, so `Snip` removes them one at a
time: a `GmCutout` records how far that has gone.  Cutting out every matte and
dualising gives the grid map.

## Main definitions

* `AdjIndex Nr` — an ordered pair `i < j` of region indices, the type indexing
  the possible adjacencies; it is a `Fintype` with decidable equality.
* `CMatte Nr`, `AdjBox Nr` — families of mattes and of adjacency boxes.
* `CMProper`, `ABProper`, `ABCMProper` — the three well-formedness conditions:
  the mattes are pairwise disjoint, the boxes are pairwise disjoint, and a
  proper box is met exactly by the two mattes it names (and by them well
  inside).
* `cmBBox` — a rectangle containing every pixel of every matte of a family.

## Main results

* `cm_extend_adj` — a well-formed family of mattes can be extended to a
  pairwise disjoint family in which every proper adjacency box gives rise to a
  genuine matte adjacency (`Matte.Adj`).
* `sub_cmBBox`, `cmBBox_proper` — the bounding box contains all the mattes and
  is nonempty.
* `card_gmdart`, `fcard_gmface`, `fcard_gmnode` — the dart, face and node
  counts of the box map.
* `cface_end0g` — two darts of the box map share a face exactly when they have
  the same start vertex.
* `gmdart_connected`, `gmdart_planar` — the box map is connected and planar.
* `gmring_cycle`, `gm_disk_def`, `disjoint_gmdisk` — the matte contours are
  face-simple ring cycles of the box map with pairwise disjoint disks.
* `has_cutout` — every matte disk can be cut out of the box map.
* `planar_bridgeless_grid_map`, `grid_map_coloring`, `exists_grid_map` — the
  grid map is planar and bridgeless, and four-colouring it colours the mattes.

## References

Gonthier's `theories/proof/gridmap.v`.
-/

namespace FourColor

/-! ### Decidability of the basic predicates -/

/-- Properness of a rectangle is decidable: it is a numeric inequality. -/
instance (r : GRect) : Decidable r.Proper := Nat.decLt 0 r.area

/-- Matte adjacency is decidable: it is a bounded search over the two rings. -/
instance (m₁ m₂ : Matte) : Decidable (Matte.Adj m₁ m₂) :=
  List.decidableBEx (fun d => gedge d ∈ m₁.ring) m₂.ring

/-! ### The index types -/

variable {Nr : ℕ}

/-- An adjacency index: an ordered pair of distinct region indices.  The two
regions named by a proper adjacency box are `fst` and `snd`. -/
structure AdjIndex (Nr : ℕ) where
  /-- The smaller of the two region indices. -/
  fst : Fin Nr
  /-- The larger of the two region indices. -/
  snd : Fin Nr
  /-- The indices are ordered, hence distinct. -/
  lt : fst < snd

namespace AdjIndex

/-- Two adjacency indices with the same components are equal. -/
theorem ext' {e f : AdjIndex Nr} (h₁ : e.fst = f.fst) (h₂ : e.snd = f.snd) : e = f := by
  cases e; cases f; cases h₁; cases h₂; rfl

/-- The components of an adjacency index are distinct. -/
theorem fst_ne_snd (e : AdjIndex Nr) : e.fst ≠ e.snd := ne_of_lt e.lt

/-- A region index is incident to an adjacency index when it is one of its two
components. -/
def Incident (e : AdjIndex Nr) (i : Fin Nr) : Prop := i = e.fst ∨ i = e.snd

theorem incident_fst (e : AdjIndex Nr) : e.Incident e.fst := Or.inl rfl

theorem incident_snd (e : AdjIndex Nr) : e.Incident e.snd := Or.inr rfl

instance : DecidableEq (AdjIndex Nr) := fun e f =>
  if h : e.fst = f.fst ∧ e.snd = f.snd then isTrue (ext' h.1 h.2)
  else isFalse fun hc => h (by cases hc; exact ⟨rfl, rfl⟩)

/-- Adjacency indices are the pairs of an ordered pair type, hence finite. -/
def equivSubtype : AdjIndex Nr ≃ {p : Fin Nr × Fin Nr // p.1 < p.2} where
  toFun e := ⟨(e.fst, e.snd), e.lt⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (AdjIndex Nr) := Fintype.ofEquiv _ equivSubtype.symm

end AdjIndex

/-- A family of `Nr` grid regions. -/
def CMatte (Nr : ℕ) : Type := Fin Nr → Matte

/-- A family of adjacency boxes, one grid rectangle per ordered pair of region
indices.  An improper rectangle means "not adjacent". -/
def AdjBox (Nr : ℕ) : Type := AdjIndex Nr → GRect

/-! ### Well-formedness -/

/-- The mattes of a family are pairwise disjoint. -/
def CMProper (cm : CMatte Nr) : Prop :=
  ∀ i j : Fin Nr, (∃ p ∈ (cm i).disk, p ∈ (cm j).disk) → i = j

/-- The adjacency boxes of a family are pairwise disjoint. -/
def ABProper (ab : AdjBox Nr) : Prop :=
  ∀ (e f : AdjIndex Nr) (p : GPoint), p ∈ (ab e).toRegion → p ∈ (ab f).toRegion → e = f

/-- A proper adjacency box is met well inside by each of the two mattes it
names, and is avoided altogether by every other matte. -/
def ABCMProper (ab : AdjBox Nr) (cm : CMatte Nr) (e : AdjIndex Nr) (i : Fin Nr) : Prop :=
  (ab e).Proper →
    (e.Incident i → ∃ p ∈ (cm i).disk, p ∈ (ab e).inset.toRegion) ∧
      ((∃ p ∈ (cm i).disk, p ∈ (ab e).toRegion) → e.Incident i)

/-! ### Extending the mattes to realise the adjacencies

An adjacency index is *apart* for a family of mattes when its box is proper —
so an adjacency is prescribed — but the two mattes are not yet adjacent.  The
extension procedure removes apart indices one at a time.
-/

/-- The box of `e` prescribes an adjacency that `cm` does not yet realise. -/
def Apart (ab : AdjBox Nr) (cm : CMatte Nr) (e : AdjIndex Nr) : Prop :=
  (ab e).Proper ∧ ¬ Matte.Adj (cm e.fst) (cm e.snd)

instance (ab : AdjBox Nr) (cm : CMatte Nr) : DecidablePred (Apart ab cm) :=
  fun _ => instDecidableAnd

/-- The finite set of adjacencies still to be realised; the extension procedure
makes it strictly smaller at each step. -/
def apartFinset (ab : AdjBox Nr) (cm : CMatte Nr) : Finset (AdjIndex Nr) :=
  Finset.univ.filter (Apart ab cm)

theorem mem_apartFinset {ab : AdjBox Nr} {cm : CMatte Nr} {e : AdjIndex Nr} :
    e ∈ apartFinset ab cm ↔ Apart ab cm e := by
  simp [apartFinset]

/-- The invariant carried through the extension: at every still-unrealised
adjacency, each of the two named mattes is coarse in the box and meets its
inset, and no other matte meets the box at all. -/
def ExtInvariant (ab : AdjBox Nr) (cm : CMatte Nr) : Prop :=
  ∀ (e : AdjIndex Nr) (i : Fin Nr), Apart ab cm e →
    (e.Incident i → CoarseIn (ab e).toRegion (cm i) ∧
        ∃ p ∈ (cm i).disk, p ∈ (ab e).inset.toRegion) ∧
      ((∃ p ∈ (cm i).disk, p ∈ (ab e).toRegion) → e.Incident i)

/-- The extension procedure.  `hcoarseBox` says that membership in a box only
depends on the coarse pixel, which holds for the once-refined boxes we use it
for; it is what lets the extension stay coarse in the *other* boxes. -/
private theorem extend_aux {ab : AdjBox Nr} (habP : ABProper ab)
    (hcoarseBox : ∀ (e : AdjIndex Nr) (p q : GPoint), halfg p = halfg q →
      p ∈ (ab e).toRegion → q ∈ (ab e).toRegion) :
    ∀ (n : ℕ) (cm : CMatte Nr), (apartFinset ab cm).card ≤ n → CMProper cm →
      ExtInvariant ab cm →
      ∃ xcm : CMatte Nr, CMProper xcm ∧
        ∀ e : AdjIndex Nr, (ab e).Proper → Matte.Adj (xcm e.fst) (xcm e.snd) := by
  intro n
  induction n with
  | zero =>
    intro cm hcard hcmP _
    refine ⟨cm, hcmP, fun e hep => ?_⟩
    by_contra hadj
    have hmem : e ∈ apartFinset ab cm := mem_apartFinset.mpr ⟨hep, hadj⟩
    have := Finset.card_pos.mpr ⟨e, hmem⟩
    omega
  | succ n ih =>
    intro cm hcard hcmP hinv
    by_cases hempty : ∀ e : AdjIndex Nr, ¬ Apart ab cm e
    · exact ⟨cm, hcmP, fun e hep => by
        by_contra hadj; exact hempty e ⟨hep, hadj⟩⟩
    push Not at hempty
    obtain ⟨e, he⟩ := hempty
    have hij : e.fst ≠ e.snd := e.fst_ne_snd
    -- The two named mattes meet the inset of the box, and the second is coarse there.
    obtain ⟨-, p₁, hp₁d, hp₁i⟩ := (hinv e e.fst he).1 e.incident_fst
    obtain ⟨hcoarse₂, p₂, hp₂d, hp₂i⟩ := (hinv e e.snd he).1 e.incident_snd
    -- Grow the second matte inside the box until it touches the first.
    obtain ⟨cm2, hsub2, hcm2, hadj2⟩ :=
      extend_madj (m := cm e.snd) (m1 := cm e.fst) (r := ab e) hcoarse₂
        ⟨p₂, hp₂d, GRect.mem_of_mem_inset hp₂i⟩ ⟨p₁, hp₁d, hp₁i⟩
        (fun q hq hq1 => hij (hcmP _ _ ⟨q, hq1, hq⟩))
    obtain ⟨xcm, hxj, hxi⟩ :
        ∃ xcm : CMatte Nr, xcm e.snd = cm2 ∧ ∀ i, i ≠ e.snd → xcm i = cm i :=
      ⟨fun i => if i = e.snd then cm2 else cm i, by simp, fun i hi => by simp [hi]⟩
    -- The grown matte still misses every other matte of the family.
    have hnot2 : ∀ i, i ≠ e.snd → ∀ q ∈ cm2.disk, q ∉ (cm i).disk := by
      intro i hi q hq hqi
      obtain ⟨hor, hnot₁⟩ := hcm2 q hq
      by_cases hie : i = e.fst
      · exact hnot₁ (hie ▸ hqi)
      · rcases hor with hab | hj
        · rcases (hinv e i he).2 ⟨q, hqi, hab⟩ with h | h
          · exact hie h
          · exact hi h
        · exact hi (hcmP i e.snd ⟨q, hqi, hj⟩)
    have hxP : CMProper xcm := by
      rintro i j ⟨p, hpi, hpj⟩
      by_cases hi : i = e.snd
      · by_cases hj : j = e.snd
        · rw [hi, hj]
        · rw [hi, hxj] at hpi
          rw [hxi j hj] at hpj
          exact absurd hpj (hnot2 j hj p hpi)
      · by_cases hj : j = e.snd
        · rw [hj, hxj] at hpj
          rw [hxi i hi] at hpi
          exact absurd hpi (hnot2 i hi p hpj)
        · rw [hxi i hi] at hpi
          rw [hxi j hj] at hpj
          exact hcmP i j ⟨p, hpi, hpj⟩
    -- Growing the matte cannot destroy an adjacency it already had.
    have hadjcm2 : ∀ i, i ≠ e.snd → Matte.Adj (cm i) (cm e.snd) → Matte.Adj (cm i) cm2 := by
      rintro i hi ⟨d, hd, hed⟩
      have hd' := ((cm e.snd).mem_ring d).mp hd
      have hed' := ((cm i).mem_ring _).mp hed
      simp only [gborder, Set.mem_ofPred_eq] at hd' hed'
      exact ⟨d, (cm2.mem_ring d).mpr
        ⟨hsub2 _ hd'.1, fun hc => hnot2 i hi _ hc hed'.1⟩, hed⟩
    have hsubapart : ∀ f : AdjIndex Nr, Apart ab xcm f → Apart ab cm f := by
      rintro f ⟨hfp, hfadj⟩
      refine ⟨hfp, fun hc => hfadj ?_⟩
      by_cases h₁ : f.fst = e.snd
      · have h₂ : f.snd ≠ e.snd := fun hc' => f.fst_ne_snd (h₁.trans hc'.symm)
        rw [h₁, hxj, hxi _ h₂]
        rw [h₁] at hc
        exact Matte.adj_symm (hadjcm2 f.snd h₂ (Matte.adj_symm hc))
      · by_cases h₂ : f.snd = e.snd
        · rw [hxi _ h₁, h₂, hxj]
          exact hadjcm2 f.fst h₁ (h₂ ▸ hc)
        · rw [hxi _ h₁, hxi _ h₂]; exact hc
    have henot : ¬ Apart ab xcm e := by
      rintro ⟨-, hn⟩
      exact hn (by rw [hxi _ hij, hxj]; exact hadj2)
    have hcard' : (apartFinset ab xcm).card ≤ n := by
      have hsub : apartFinset ab xcm ⊆ apartFinset ab cm := fun f hf =>
        mem_apartFinset.mpr (hsubapart f (mem_apartFinset.mp hf))
      have hmem : e ∈ apartFinset ab cm := mem_apartFinset.mpr he
      have hlt : (apartFinset ab xcm).card < (apartFinset ab cm).card :=
        Finset.card_lt_card ⟨hsub, fun hc => henot (mem_apartFinset.mp (hc hmem))⟩
      omega
    refine ih xcm hcard' hxP ?_
    -- The invariant survives the extension.
    intro f i hf
    have hfcm : Apart ab cm f := hsubapart f hf
    have hfe : f ≠ e := by rintro rfl; exact henot hf
    have hbf : ∀ q, q ∈ (ab e).toRegion → q ∉ (ab f).toRegion := fun q hqe hqf =>
      hfe (habP e f q hqe hqf).symm
    by_cases hi : i = e.snd
    · rw [hi, hxj]
      obtain ⟨hA, hB⟩ := hinv f e.snd hfcm
      refine ⟨fun hinc => ?_, ?_⟩
      · obtain ⟨hcoarse, p, hpd, hpi⟩ := hA hinc
        refine ⟨fun p hp q hq => ?_, p, hsub2 p hpd, hpi⟩
        have hqf : q ∈ (ab f).toRegion := hcoarseBox f p q hq.symm hp
        constructor
        · intro hqd
          rcases (hcm2 q hqd).1 with hae | hjd
          · exact absurd hqf (hbf q hae)
          · exact hsub2 p ((hcoarse p hp q hq).mp hjd)
        · intro hpd'
          rcases (hcm2 p hpd').1 with hae | hjd
          · exact absurd hp (hbf p hae)
          · exact hsub2 q ((hcoarse p hp q hq).mpr hjd)
      · rintro ⟨p, hpd, hpf⟩
        rcases (hcm2 p hpd).1 with hae | hjd
        · exact absurd hpf (hbf p hae)
        · exact hB ⟨p, hjd, hpf⟩
    · rw [hxi i hi]
      exact hinv f i hfcm

/-- **The extension theorem.**  A well-formed family of mattes can be extended
to a pairwise disjoint family in which every prescribed adjacency is realised
as a genuine shared contour edge. -/
theorem cm_extend_adj {ab0 : AdjBox Nr} {cm0 : CMatte Nr} (hab0 : ABProper ab0)
    (hcm0 : CMProper cm0) (habcm0 : ∀ e i, ABCMProper ab0 cm0 e i) :
    ∃ cm : CMatte Nr, CMProper cm ∧
      ∀ e : AdjIndex Nr, (ab0 e).Proper → Matte.Adj (cm e.fst) (cm e.snd) := by
  -- Refine the grid once: this makes every matte coarse, hence extendable.
  set ab : AdjBox Nr := fun e => refineRect (ab0 e) with hab
  set cm1 : CMatte Nr := fun i => refineMatte (cm0 i) with hcm1
  have habP : ABProper ab := by
    intro e f p hpe hpf
    exact hab0 e f (halfg p) ((mem_refineRect _ _).mp hpe) ((mem_refineRect _ _).mp hpf)
  have hcoarseBox : ∀ (e : AdjIndex Nr) (p q : GPoint), halfg p = halfg q →
      p ∈ (ab e).toRegion → q ∈ (ab e).toRegion := by
    intro e p q hpq hp
    rw [hab, mem_refineRect] at hp ⊢
    rwa [← hpq]
  have hcm1P : CMProper cm1 := by
    rintro i j ⟨p, hpi, hpj⟩
    exact hcm0 i j ⟨halfg p, mem_refineMatte.mp hpi, mem_refineMatte.mp hpj⟩
  have hinv : ExtInvariant ab cm1 := by
    intro e i hape
    have hprop : (ab0 e).Proper := (proper_refineRect (ab0 e)).mp hape.1
    obtain ⟨hA, hB⟩ := habcm0 e i hprop
    refine ⟨fun hinc => ⟨refineMatte_coarseIn _ _, ?_⟩, ?_⟩
    · obtain ⟨p, hpd, hpi⟩ := hA hinc
      refine ⟨p + p, by rw [hcm1, mem_refineMatte, halfg_double]; exact hpd, ?_⟩
      have h1 : p + p ∈ (refineRect (ab0 e).inset).toRegion := by
        rw [mem_refineRect, halfg_double]; exact hpi
      rw [refine_inset] at h1
      exact GRect.mem_of_mem_inset h1
    · rintro ⟨p, hpd, hpr⟩
      exact hB ⟨halfg p, mem_refineMatte.mp hpd, (mem_refineRect _ _).mp hpr⟩
  obtain ⟨cm, hcmP, hadj⟩ := extend_aux habP hcoarseBox _ cm1 le_rfl hcm1P hinv
  exact ⟨cm, hcmP, fun e hep => hadj e ((proper_refineRect (ab0 e)).mpr hep)⟩

/-! ### The bounding box

The remaining construction of `gridmap.v` frames a bounding box of the extended
mattes to get a plain planar connected map.  Here is that box.
-/

/-- All the pixels of all the mattes of a family. -/
def cmPixels (cm : CMatte Nr) : Finset GPoint :=
  (Finset.univ : Finset (Fin Nr)).biUnion fun i => (cm i).disk

theorem mem_cmPixels {cm : CMatte Nr} {p : GPoint} :
    p ∈ cmPixels cm ↔ ∃ i, p ∈ (cm i).disk := by
  simp [cmPixels]

/-- A grid rectangle containing every pixel of every matte of the family.  The
seed rectangle is the unit square, so the result is always proper. -/
noncomputable def cmBBox (cm : CMatte Nr) : GRect :=
  (cmPixels cm).toList.foldr extendGRect ⟨0, 1, 0, 1⟩

/-- The seed of a `foldr` of `extendGRect` is contained in the result. -/
private theorem subset_foldr_extendGRect (l : List GPoint) (r : GRect) :
    r.toRegion ⊆ (l.foldr extendGRect r).toRegion := by
  induction l with
  | nil => exact fun _ h => h
  | cons q l ih => exact fun p hp => subset_extendGRect q _ (ih hp)

/-- Every point folded into the rectangle lands in it. -/
private theorem mem_foldr_extendGRect {l : List GPoint} {p : GPoint} (hp : p ∈ l)
    (r : GRect) : p ∈ (l.foldr extendGRect r).toRegion := by
  induction l with
  | nil => exact absurd hp (List.not_mem_nil)
  | cons q l ih =>
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact mem_extendGRect_self p _
    · exact subset_extendGRect q _ (ih hp')

/-- The bounding box contains every matte of the family. -/
theorem sub_cmBBox (cm : CMatte Nr) (i : Fin Nr) {p : GPoint} (hp : p ∈ (cm i).disk) :
    p ∈ (cmBBox cm).toRegion :=
  mem_foldr_extendGRect (Finset.mem_toList.mpr (mem_cmPixels.mpr ⟨i, hp⟩)) _

/-- The bounding box is nonempty. -/
theorem cmBBox_proper (cm : CMatte Nr) : (cmBBox cm).Proper := by
  rw [GRect.proper_iff_nonempty]
  refine ⟨(0, 0), subset_foldr_extendGRect _ ⟨0, 1, 0, 1⟩ ?_⟩
  exact ⟨le_rfl, by norm_num, le_rfl, by norm_num⟩

/-! ### The box hypermap

The darts of the box map are the darts of the (refined) bounding box together
with their edge mates.  Taking the edge closure is what makes the map
bridgeless: the map on the box alone has the frame darts for bridges.

`gmedge` is the grid edge map, which preserves this dart set.  The other two
permutations follow the grid ones as far as they can: `gmface u` is the last of
`gnode u`, `gnode² u`, `gnode³ u` that is still a dart of the map — recall that
in the grid map `gface (gedge d) = gnode⁻¹ d` — and `gmnode` is its inverse
recipe.  Off the frame the two agree with `gface` and `gedge ∘ gnode`.
-/

variable {bb : GRect}

/-- The darts of the box map: those of the refined box, edge-closed. -/
def gmgrid (bb : GRect) : Finset GPoint :=
  (refineRect bb).toFinset ∪ (refineRect bb).toFinset.image gedge

theorem mem_gmgrid {d : GPoint} :
    d ∈ gmgrid bb ↔ halfg d ∈ bb.toRegion ∨ halfg (gedge d) ∈ bb.toRegion := by
  simp only [gmgrid, Finset.mem_union, Finset.mem_image, GRect.mem_toFinset, mem_refineRect]
  constructor
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rwa [gedge2])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨gedge d, h, gedge2 d⟩

/-- The dart set is closed under `gedge`. -/
theorem gedge_mem_gmgrid {d : GPoint} : gedge d ∈ gmgrid bb ↔ d ∈ gmgrid bb := by
  rw [mem_gmgrid, mem_gmgrid, gedge2, or_comm]

/-- The darts of the box map. -/
abbrev GmDart (bb : GRect) : Type := {d : GPoint // d ∈ gmgrid bb}

/-- The edge permutation of the box map. -/
def gmedge (u : GmDart bb) : GmDart bb := ⟨gedge u.1, gedge_mem_gmgrid.mpr u.2⟩

@[simp] theorem gmedge_val (u : GmDart bb) : (gmedge u).1 = gedge u.1 := rfl

/-- The face permutation of the box map: the last of the three `gnode` iterates
of `u` that is still a dart of the map. -/
def gmface (u : GmDart bb) : GmDart bb :=
  if h₃ : gnode (gnode (gnode u.1)) ∈ gmgrid bb then ⟨gnode (gnode (gnode u.1)), h₃⟩
  else if h₂ : gnode (gnode u.1) ∈ gmgrid bb then ⟨gnode (gnode u.1), h₂⟩
  else if h₁ : gnode u.1 ∈ gmgrid bb then ⟨gnode u.1, h₁⟩
  else u

/-- The node permutation of the box map: the first `gedge`-image of a `gnode`
iterate of `u` that is still a dart of the map. -/
def gmnode (u : GmDart bb) : GmDart bb :=
  if h₁ : gedge (gnode u.1) ∈ gmgrid bb then ⟨gedge (gnode u.1), h₁⟩
  else if h₂ : gedge (gnode (gnode u.1)) ∈ gmgrid bb then ⟨gedge (gnode (gnode u.1)), h₂⟩
  else if h₃ : gedge (gnode (gnode (gnode u.1))) ∈ gmgrid bb then
    ⟨gedge (gnode (gnode (gnode u.1))), h₃⟩
  else u

theorem gmface_val (u : GmDart bb) :
    (gmface u).1 =
      if gnode (gnode (gnode u.1)) ∈ gmgrid bb then gnode (gnode (gnode u.1))
      else if gnode (gnode u.1) ∈ gmgrid bb then gnode (gnode u.1)
      else if gnode u.1 ∈ gmgrid bb then gnode u.1 else u.1 := by
  simp only [gmface]
  split_ifs <;> rfl

theorem gmnode_val (u : GmDart bb) :
    (gmnode u).1 =
      if gedge (gnode u.1) ∈ gmgrid bb then gedge (gnode u.1)
      else if gedge (gnode (gnode u.1)) ∈ gmgrid bb then gedge (gnode (gnode u.1))
      else if gedge (gnode (gnode (gnode u.1))) ∈ gmgrid bb then
        gedge (gnode (gnode (gnode u.1)))
      else u.1 := by
  simp only [gmnode]
  split_ifs <;> rfl

/-- The pixel of a dart is unchanged by `gedge ∘ gnode`. -/
theorem halfg_gedge_gnode (d : GPoint) : halfg (gedge (gnode d)) = halfg d := by
  rw [← halfg_gface, gface_gedge_gnode]

/-- The three permutations satisfy the defining hypermap identity. -/
theorem gmedgeK (u : GmDart bb) : gmnode (gmface (gmedge u)) = u := by
  refine Subtype.ext ?_
  have hd : u.1 ∈ gmgrid bb := u.2
  have e3 : gnode (gnode (gnode (gedge u.1))) = gface u.1 := by
    rw [← gnode_gface u.1, gnode4]
  have e4 : gnode (gface u.1) = gedge u.1 := gnode_gface u.1
  by_cases h₃ : gface u.1 ∈ gmgrid bb
  · have hw : (gmface (gmedge u)).1 = gface u.1 := by
      rw [gmface_val, gmedge_val, e3, ite_eq_left h₃]
    rw [gmnode_val, hw, e4, gedge2 u.1, ite_eq_left hd]
  · -- The face dart is off the map, so `u` is a frame dart pointing outwards.
    have hbb : halfg (gedge u.1) ∈ bb.toRegion := by
      rcases mem_gmgrid.mp hd with h | h
      · exact absurd (mem_gmgrid.mpr (Or.inl (by rwa [halfg_gface]))) h₃
      · exact h
    have hc₃ : gedge (gface u.1) ∉ gmgrid bb := fun h => h₃ (gedge_mem_gmgrid.mp h)
    by_cases h₂ : gnode (gnode (gedge u.1)) ∈ gmgrid bb
    · have hw : (gmface (gmedge u)).1 = gnode (gnode (gedge u.1)) := by
        rw [gmface_val, gmedge_val, e3, ite_eq_right h₃, ite_eq_left h₂]
      rw [gmnode_val, hw, e3, e4, gedge2 u.1, ite_eq_right hc₃, ite_eq_left hd]
    · -- Only the first iterate is left, and it is always a dart of the map.
      have h₁ : gnode (gedge u.1) ∈ gmgrid bb := by
        refine mem_gmgrid.mpr (Or.inr ?_)
        rw [halfg_gedge_gnode]
        exact hbb
      have hw : (gmface (gmedge u)).1 = gnode (gedge u.1) := by
        rw [gmface_val, gmedge_val, e3, ite_eq_right h₃, ite_eq_right h₂, ite_eq_left h₁]
      have hc₂ : gedge (gnode (gnode (gedge u.1))) ∉ gmgrid bb := fun h =>
        h₂ (gedge_mem_gmgrid.mp h)
      rw [gmnode_val, hw, e3, e4, gedge2 u.1, ite_eq_right hc₂, ite_eq_right hc₃, ite_eq_left hd]

/-- The box hypermap: a plain map on the edge closure of a refined rectangle. -/
noncomputable def gmdartMap (bb : GRect) : Hypermap (GmDart bb) :=
  Hypermap.ofCancel3 gmedge gmnode gmface gmedgeK

@[simp] theorem gmdartMap_edge (u : GmDart bb) : (gmdartMap bb).edge u = gmedge u := rfl

@[simp] theorem gmdartMap_node (u : GmDart bb) : (gmdartMap bb).node u = gmnode u := rfl

@[simp] theorem gmdartMap_face (u : GmDart bb) : (gmdartMap bb).face u = gmface u := rfl

/-- The box map is plain: `gedge` is a fixed-point-free involution. -/
theorem plain_gmdartMap (bb : GRect) : (gmdartMap bb).Plain where
  edge_edge u := Subtype.ext (gedge2 u.1)
  edge_ne u h := halfg_gedge_ne u.1 (congrArg halfg (congrArg Subtype.val h))

/-! ### The inside of the box

A dart is *inner* when its own pixel lies in the box; the frame darts are the
others.  On inner darts the node permutation is the grid one, `gedge ∘ gnode`.
-/

/-- The darts whose pixel lies in the bounding box. -/
def GmInner (bb : GRect) (u : GmDart bb) : Prop := halfg u.1 ∈ bb.toRegion

theorem gmInner_or_gmInner_gmedge (u : GmDart bb) :
    GmInner bb u ∨ GmInner bb (gmedge u) := mem_gmgrid.mp u.2

/-- On an inner dart the node permutation is the grid one. -/
theorem gmnode_val_of_inner {u : GmDart bb} (h : GmInner bb u) :
    (gmnode u).1 = gedge (gnode u.1) := by
  rw [gmnode_val, ite_eq_left (mem_gmgrid.mpr (Or.inl (by rwa [halfg_gedge_gnode])))]

/-- The inside of the box is closed under the node permutation. -/
theorem gmInner_gmnode {u : GmDart bb} (h : GmInner bb u) : GmInner bb (gmnode u) := by
  simpa [GmInner, gmnode_val_of_inner h, halfg_gedge_gnode] using h


/-! ### Counting the darts of the box map

The box map has `4 * w * h` inner darts, four for each pixel of the `w × h`
box, together with one frame dart for each pixel on each of the four sides of
the box, so `2 * (w + h)` of those.
-/

/-- The four parities of a dart, as a finite set. -/
private def oddgs : Finset GPoint := {(0, 0), (1, 0), (1, 1), (0, 1)}

/-- `oddgs` is exactly the set of parities. -/
private theorem mem_oddgs {c : GPoint} : c ∈ oddgs ↔ IsOddg c := by
  obtain ⟨x, y⟩ := c
  change _ ↔ (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)
  simp only [oddgs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- A parity is one of the four corners of the unit square. -/
private theorem isOddg_cases {c : GPoint} (hc : IsOddg c) :
    c = (0, 0) ∨ c = (1, 0) ∨ c = (1, 1) ∨ c = (0, 1) := by
  have h := mem_oddgs.mpr hc
  simpa only [oddgs, Finset.mem_insert, Finset.mem_singleton] using h

/-- The displacement from the pixel of a dart to the pixel across its edge,
as a function of the dart's parity. -/
private def gdir (c : GPoint) : GPoint :=
  if c = (0, 0) then (0, -1) else if c = (1, 0) then (1, 0)
  else if c = (1, 1) then (0, 1) else (-1, 0)

/-- The edge of a dart leads to the neighbouring pixel in direction `gdir`. -/
private theorem halfg_gedge_gdir (d : GPoint) :
    halfg (gedge d) = halfg d + gdir (oddg d) := by
  rw [halfg_gedge]
  rcases isOddg_cases (oddgP d) with h | h | h | h <;> rw [h] <;>
    norm_num [gdir, arcg, ccw, Prod.ext_iff] <;> omega

/-- One of the four sides of the box: the pixels of `bb` whose neighbour in
direction `gdir c` lies outside `bb`. -/
private def gmSide (bb : GRect) (c : GPoint) : GRect :=
  if c = (0, 0) then ⟨bb.xmin, bb.xmax, bb.ymin, bb.ymin + 1⟩
  else if c = (1, 0) then ⟨bb.xmax - 1, bb.xmax, bb.ymin, bb.ymax⟩
  else if c = (1, 1) then ⟨bb.xmin, bb.xmax, bb.ymax - 1, bb.ymax⟩
  else ⟨bb.xmin, bb.xmin + 1, bb.ymin, bb.ymax⟩

/-- The side `gmSide bb c` consists exactly of the pixels of `bb` whose
`gdir c` neighbour has left the box. -/
private theorem mem_gmSide (hbb : bb.Proper) {c : GPoint} (hc : c ∈ oddgs) (p : GPoint) :
    p ∈ (gmSide bb c).toRegion ↔ p ∈ bb.toRegion ∧ p + gdir c ∉ bb.toRegion := by
  obtain ⟨hx, hy⟩ := (GRect.proper_iff bb).mp hbb
  rcases isOddg_cases (mem_oddgs.mp hc) with rfl | rfl | rfl | rfl <;>
    norm_num [gmSide, gdir, GRect.mem_toRegion, Prod.ext_iff] <;> omega

/-- The inner darts whose edge mate has left the box. -/
private def gmFrameIn (bb : GRect) : Finset GPoint :=
  (refineRect bb).toFinset.filter fun d => halfg (gedge d) ∉ bb.toFinset

private theorem mem_gmFrameIn {d : GPoint} :
    d ∈ gmFrameIn bb ↔ halfg d ∈ bb.toRegion ∧ halfg (gedge d) ∉ bb.toRegion := by
  rw [gmFrameIn, Finset.mem_filter, GRect.mem_toFinset, mem_refineRect, GRect.mem_toFinset]

/-- The frame darts split into the four sides of the box. -/
private theorem gmFrameIn_eq (hbb : bb.Proper) :
    gmFrameIn bb = oddgs.biUnion fun c => (gmSide bb c).toFinset.image fun p => p + p + c := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_image, GRect.mem_toFinset, mem_gmFrameIn]
  constructor
  · rintro ⟨h1, h2⟩
    have hd : oddg d ∈ oddgs := mem_oddgs.mpr (oddgP d)
    refine ⟨oddg d, hd, halfg d, ?_, halfgK d⟩
    rw [mem_gmSide hbb hd]
    exact ⟨h1, by rw [← halfg_gedge_gdir]; exact h2⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    have hc' : IsOddg c := mem_oddgs.mp hc
    rw [mem_gmSide hbb hc] at hp
    rw [halfg_eq hc']
    refine ⟨hp.1, ?_⟩
    rw [halfg_gedge_gdir, halfg_eq hc', oddg_eq hc']
    exact hp.2

/-- Doubling a pixel and adding a fixed parity is injective. -/
private theorem double_add_injective (c : GPoint) :
    Function.Injective fun p : GPoint => p + p + c := by
  intro p q h
  have h' : p + p = q + q := by
    simpa using congrArg (fun z : GPoint => z - c) h
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at h' ⊢
  omega

/-- There are `2 * (w + h)` frame darts. -/
private theorem card_gmFrameIn (hbb : bb.Proper) :
    (gmFrameIn bb).card = 2 * (bb.width + bb.height) := by
  obtain ⟨hx, hy⟩ := (GRect.proper_iff bb).mp hbb
  rw [gmFrameIn_eq hbb, Finset.card_biUnion]
  · have hcard : ∀ c ∈ oddgs,
        ((gmSide bb c).toFinset.image fun p => p + p + c).card = (gmSide bb c).area := by
      intro c _
      rw [Finset.card_image_of_injective _ (double_add_injective c), GRect.card_toFinset]
    rw [Finset.sum_congr rfl hcard]
    simp only [oddgs]
    rw [Finset.sum_insert (by norm_num [Prod.ext_iff]),
      Finset.sum_insert (by norm_num [Prod.ext_iff]),
      Finset.sum_insert (by norm_num [Prod.ext_iff]), Finset.sum_singleton]
    norm_num [gmSide, GRect.area, GRect.width, GRect.height, zwidth, Prod.ext_iff]
    omega
  · intro c hc c' hc' hne
    refine Finset.disjoint_left.mpr ?_
    rintro d hd hd'
    simp only [Finset.mem_image] at hd hd'
    obtain ⟨p, -, rfl⟩ := hd
    obtain ⟨q, -, hq⟩ := hd'
    have h1 : oddg (p + p + c) = c := oddg_eq (mem_oddgs.mp hc)
    have h2 : oddg (q + q + c') = c' := oddg_eq (mem_oddgs.mp hc')
    exact hne (by rw [← h1, ← hq, h2])

/-- **The dart count of the box map.** -/
theorem card_gmdart (hbb : bb.Proper) :
    Nat.card (GmDart bb) = 2 * (2 * (bb.width * bb.height) + bb.width + bb.height) := by
  have hcard : Nat.card (GmDart bb) = (gmgrid bb).card := by
    simp [GmDart, Nat.card_eq_fintype_card]
  have hginj : Function.Injective gedge := Function.LeftInverse.injective gedge2
  have hsplit : gmgrid bb =
      (refineRect bb).toFinset ∪ ((gmFrameIn bb).image gedge) := by
    ext d
    simp only [gmgrid, Finset.mem_union, Finset.mem_image, GRect.mem_toFinset,
      mem_refineRect, mem_gmFrameIn]
    constructor
    · rintro (h | ⟨e, he, rfl⟩)
      · exact Or.inl h
      · by_cases hd : halfg (gedge e) ∈ bb.toRegion
        · exact Or.inl hd
        · exact Or.inr ⟨e, ⟨he, hd⟩, rfl⟩
    · rintro (h | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e, he, rfl⟩
  have hdisj : Disjoint (refineRect bb).toFinset ((gmFrameIn bb).image gedge) := by
    refine Finset.disjoint_left.mpr ?_
    intro d hd hd'
    simp only [Finset.mem_image, mem_gmFrameIn] at hd'
    obtain ⟨e, ⟨-, he⟩, rfl⟩ := hd'
    exact he ((GRect.mem_toFinset _ _).mp hd |> (mem_refineRect bb _).mp)
  rw [hcard, hsplit, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hginj, card_gmFrameIn hbb, GRect.card_toFinset,
    area_refineRect, GRect.area]
  ring


/-! ### Faces of the box map

The face permutation follows `gnode`, which fixes the *start vertex* `end0g` of
a dart, so two darts lie on a common face exactly when they share their start
vertex.  There are four darts with a given start vertex, and `gmface` runs
through those of them that are darts of the box map.
-/

/-- The start vertex of a dart is unchanged by `gnode`. -/
theorem end0g_gnode (d : GPoint) : end0g (gnode d) = end0g d := by
  have h3 : end0g (gnode d) = halfg (gnode d) + oddg (gnode d) := rfl
  have h4 : end0g d = halfg d + oddg d := rfl
  have h5 : arcg (oddg d) = ccw (oddg d) - oddg d := rfl
  rw [h3, h4, halfg_gnode, oddg_gnode, h5]
  abel

/-- The start vertex is constant along `gnode` orbits. -/
private theorem end0g_gnode_iter (k : ℕ) (d : GPoint) : end0g (gnode^[k] d) = end0g d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', end0g_gnode, ih]

/-- The parity turns by a quarter at each `gnode` step. -/
private theorem oddg_gnode_iter (k : ℕ) (d : GPoint) :
    oddg (gnode^[k] d) = ccw^[k] (oddg d) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', oddg_gnode, ih, Function.iterate_succ_apply']

/-- Two darts with the same start vertex differ by a rotation about it. -/
theorem exists_iter_gnode {d₁ d₂ : GPoint} (h : end0g d₁ = end0g d₂) :
    ∃ i < 4, gnode^[i] d₁ = d₂ := by
  obtain ⟨i, hi, hci⟩ := exists_iter_ccw (oddgP d₁) (oddgP d₂)
  refine ⟨i, hi, ?_⟩
  have h2 : oddg (gnode^[i] d₁) = oddg d₂ := by rw [oddg_gnode_iter, hci]
  have h1 : end0g (gnode^[i] d₁) = end0g d₂ := by rw [end0g_gnode_iter]; exact h
  have hh : halfg (gnode^[i] d₁) = halfg d₂ := by
    simp only [end0g, h2] at h1
    exact add_right_cancel h1
  have hkey : gnode^[i] d₁ = halfg d₂ + halfg d₂ + oddg d₂ := by
    rw [← hh, ← h2]; exact (halfgK _).symm
  rw [hkey, halfgK]

/-- The face permutation of the box map preserves the start vertex. -/
theorem end0g_gmface (u : GmDart bb) : end0g (gmface u).1 = end0g u.1 := by
  rw [gmface_val]
  split_ifs <;> simp only [end0g_gnode]

/-- If a rotation of a dart of the box map is again a dart of the map, and no
earlier rotation is, then one `gmface` step goes back from it. -/
private theorem gmface_of_min {u w : GmDart bb} {m : ℕ}
    (hm1 : 1 ≤ m) (hm3 : m ≤ 3) (hw : w.1 = gnode^[m] u.1)
    (hmin : ∀ j, 1 ≤ j → j < m → gnode^[j] u.1 ∉ gmgrid bb) :
    gmface w = u := by
  refine Subtype.ext ?_
  rw [gmface_val, hw]
  have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm with rfl | rfl | rfl
  · simp only [Function.iterate_one, gnode4]
    exact ite_eq_left u.2
  · have h1 : gnode u.1 ∉ gmgrid bb := by
      simpa only [Function.iterate_one] using hmin 1 le_rfl (by omega)
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, gnode4]
    rw [ite_eq_right h1, ite_eq_left u.2]
  · have h1 : gnode u.1 ∉ gmgrid bb := by
      simpa only [Function.iterate_one] using hmin 1 le_rfl (by omega)
    have h2 : gnode (gnode u.1) ∉ gmgrid bb := by
      simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
        hmin 2 (by omega) (by omega)
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, gnode4]
    rw [ite_eq_right h2, ite_eq_right h1, ite_eq_left u.2]

/-- Every rotation of a dart that is again a dart of the box map lies on its
face. -/
private theorem cface_iter_gnode : ∀ k : ℕ, k < 4 →
    ∀ (u : GmDart bb) (h : gnode^[k] u.1 ∈ gmgrid bb),
      (gmdartMap bb).CFace u ⟨gnode^[k] u.1, h⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk4 u h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show (⟨gnode^[0] u.1, h⟩ : GmDart bb) = u from Subtype.ext rfl]
    · classical
      obtain ⟨m, hm1, hmk, hmem, hmin⟩ :
          ∃ m, 1 ≤ m ∧ m ≤ k ∧ gnode^[m] u.1 ∈ gmgrid bb ∧
            ∀ j, 1 ≤ j → j < m → gnode^[j] u.1 ∉ gmgrid bb := by
        have hP : ∃ n : ℕ, gnode^[n + 1] u.1 ∈ gmgrid bb :=
          ⟨k - 1, by rwa [Nat.sub_add_cancel hk]⟩
        refine ⟨Nat.find hP + 1, by omega, ?_, Nat.find_spec hP, ?_⟩
        · have h2 : Nat.find hP ≤ k - 1 := Nat.find_le (by rwa [Nat.sub_add_cancel hk])
          omega
        · intro j hj1 hjm
          have h3 := Nat.find_min hP (m := j - 1) (by omega)
          rwa [Nat.sub_add_cancel hj1] at h3
      have hstep : gmface (⟨gnode^[m] u.1, hmem⟩ : GmDart bb) = u :=
        gmface_of_min hm1 (by omega) rfl hmin
      have hcf : (gmdartMap bb).CFace u ⟨gnode^[m] u.1, hmem⟩ := by
        have h0 := (gmdartMap bb).cface_face (⟨gnode^[m] u.1, hmem⟩ : GmDart bb)
        rw [(gmdartMap_face (⟨gnode^[m] u.1, hmem⟩ : GmDart bb)).trans hstep] at h0
        exact h0.symm
      rcases eq_or_lt_of_le hmk with heq | hlt
      · subst heq; exact hcf
      · have hrest : gnode^[k - m] (gnode^[m] u.1) = gnode^[k] u.1 := by
          rw [← Function.iterate_add_apply]
          congr 1
          omega
        have h' : gnode^[k - m] ((⟨gnode^[m] u.1, hmem⟩ : GmDart bb) : GPoint) ∈ gmgrid bb := by
          change gnode^[k - m] (gnode^[m] u.1) ∈ gmgrid bb
          rw [hrest]; exact h
        have hih := ih (k - m) (by omega) (by omega) ⟨gnode^[m] u.1, hmem⟩ h'
        rw [show (⟨gnode^[k - m] ((⟨gnode^[m] u.1, hmem⟩ : GmDart bb) : GPoint), h'⟩ : GmDart bb)
          = ⟨gnode^[k] u.1, h⟩ from Subtype.ext hrest] at hih
        exact hcf.trans hih

open Equiv Equiv.Perm in
/-- A function that does not change along the steps of a permutation is
constant on each of its cycles. -/
private theorem congr_of_sameCycle' {D : Type*} {α : Sort*} {f : Perm D} {F : D → α}
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
    rw [show (-(n : ℤ) - 1) = -1 + -(n : ℤ) by ring, zpow_add, zpow_neg_one, Perm.mul_apply, hinv]
    exact ih

/-- **Two darts of the box map lie on a common face exactly when they have the
same start vertex.** -/
theorem cface_end0g (u v : GmDart bb) :
    (gmdartMap bb).CFace u v ↔ end0g u.1 = end0g v.1 := by
  constructor
  · intro hcf
    refine congr_of_sameCycle' (F := fun w : GmDart bb => end0g w.1) (fun w => ?_) hcf
    rw [gmdartMap_face]
    exact end0g_gmface w
  · intro h
    obtain ⟨i, hi, hiv⟩ := exists_iter_gnode h
    have hmem : gnode^[i] u.1 ∈ gmgrid bb := by rw [hiv]; exact v.2
    have hcf := cface_iter_gnode i hi u hmem
    rwa [show (⟨gnode^[i] u.1, hmem⟩ : GmDart bb) = v from Subtype.ext hiv] at hcf


/-! ### Counting the faces and the nodes -/

private theorem gdir_00 : gdir (0, 0) = (0, -1) := by simp [gdir]
private theorem gdir_10 : gdir (1, 0) = (1, 0) := by norm_num [gdir]
private theorem gdir_11 : gdir (1, 1) = (0, 1) := by norm_num [gdir]
private theorem gdir_01 : gdir (0, 1) = (-1, 0) := by norm_num [gdir]

open Equiv Equiv.Perm in
/-- If the orbits of a permutation are exactly the fibres of a function, then
its orbit count is the size of that function's range. -/
private theorem cycleCount_eq_card_range {D α : Type*} [Finite D] {f : Perm D} {g : D → α}
    (h : ∀ x y, f.SameCycle x y ↔ g x = g y) :
    cycleCount f = Nat.card (Set.range g) := by
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun x : D => (⟨g x, x, rfl⟩ : Set.range g))
      fun a b hab => Subtype.ext ((h a b).mp hab)) ⟨?_, ?_⟩)
  · intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ fun a b hab => ?_
    exact Quotient.sound ((h a b).mpr (congrArg Subtype.val hab))
  · rintro ⟨y, x, rfl⟩
    exact ⟨Quotient.mk _ x, rfl⟩

/-- The number of pixels of a rectangle, as a cardinal of its region. -/
private theorem card_toRegion (r : GRect) : Nat.card r.toRegion = r.area := by
  have h : Nat.card r.toRegion = Nat.card {p : GPoint // p ∈ r.toFinset} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (GRect.mem_toFinset r p).symm)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_coe, GRect.card_toFinset]

/-- The grid vertices of the box: the corners of its pixels. -/
private def gmFrame (bb : GRect) : GRect := ⟨bb.xmin, bb.xmax + 1, bb.ymin, bb.ymax + 1⟩

/-- The start vertices of the darts of the box map are exactly the grid
vertices of the box. -/
private theorem range_end0g (hbb : bb.Proper) :
    Set.range (fun u : GmDart bb => end0g u.1) = (gmFrame bb).toRegion := by
  obtain ⟨hx, hy⟩ := (GRect.proper_iff bb).mp hbb
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    rcases mem_gmgrid.mp u.2 with hin | hout
    · rcases isOddg_cases (oddgP u.1) with hc | hc | hc | hc <;>
      · simp only [end0g, hc, gmFrame, GRect.mem_toRegion, Prod.fst_add, Prod.snd_add] at hin ⊢
        omega
    · rw [halfg_gedge_gdir] at hout
      rcases isOddg_cases (oddgP u.1) with hc | hc | hc | hc <;>
      · rw [hc] at hout
        simp only [gdir_00, gdir_10, gdir_11, gdir_01, GRect.mem_toRegion, Prod.fst_add,
          Prod.snd_add] at hout
        simp only [end0g, hc, gmFrame, GRect.mem_toRegion, Prod.fst_add, Prod.snd_add]
        omega
  · intro hp
    classical
    set c : GPoint := (if p.1 = bb.xmax then 1 else 0, if p.2 = bb.ymax then 1 else 0) with hc
    have hcodd : IsOddg c := by
      constructor
      · rw [hc]; dsimp only; split <;> simp
      · rw [hc]; dsimp only; split <;> simp
    have hq : p - c ∈ bb.toRegion := by
      simp only [hc, gmFrame, GRect.mem_toRegion, Prod.fst_sub, Prod.snd_sub] at hp ⊢
      split_ifs at * <;> omega
    have hd : (p - c) + (p - c) + c ∈ gmgrid bb :=
      mem_gmgrid.mpr (Or.inl (by rw [halfg_eq hcodd]; exact hq))
    refine ⟨⟨_, hd⟩, ?_⟩
    change end0g ((p - c) + (p - c) + c) = p
    rw [end0g, halfg_eq hcodd, oddg_eq hcodd, sub_add_cancel]

/-- **The face count of the box map**: one face per grid vertex of the box. -/
theorem fcard_gmface (hbb : bb.Proper) :
    cycleCount (gmdartMap bb).face = (bb.width + 1) * (bb.height + 1) := by
  obtain ⟨hx, hy⟩ := (GRect.proper_iff bb).mp hbb
  rw [cycleCount_eq_card_range (f := (gmdartMap bb).face)
    (g := fun u : GmDart bb => end0g u.1) (fun u v => cface_end0g u v),
    range_end0g hbb, card_toRegion]
  have e1 : (gmFrame bb).width = bb.width + 1 := by
    simp only [gmFrame, GRect.width, zwidth]; omega
  have e2 : (gmFrame bb).height = bb.height + 1 := by
    simp only [gmFrame, GRect.height, zwidth]; omega
  rw [GRect.area, e1, e2]

/-- The node permutation of the box map is injective. -/
private theorem gmnode_injective : Function.Injective (gmnode : GmDart bb → GmDart bb) :=
  fun _ _ hab => (gmdartMap bb).node.injective (by rw [gmdartMap_node, gmdartMap_node]; exact hab)

/-- The node permutation preserves the inside and the frame of the box. -/
private theorem gmInner_gmnode_iff (u : GmDart bb) : GmInner bb (gmnode u) ↔ GmInner bb u := by
  classical
  refine ⟨fun h => ?_, gmInner_gmnode⟩
  set I : Finset (GmDart bb) := Finset.univ.filter (GmInner bb) with hI
  have hmaps : I.image gmnode ⊆ I := by
    intro v hv
    simp only [hI, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    exact gmInner_gmnode hw
  have hcard : (I.image gmnode).card = I.card :=
    Finset.card_image_of_injective _ gmnode_injective
  have heq : I.image gmnode = I := Finset.eq_of_subset_of_card_le hmaps (le_of_eq hcard.symm)
  have hmemI : gmnode u ∈ I := by
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  rw [← heq, Finset.mem_image] at hmemI
  obtain ⟨w, hw, hwu⟩ := hmemI
  simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rwa [gmnode_injective hwu] at hw

/-- The node permutation restricted to the inside of the box. -/
private noncomputable def gmnodeInner (bb : GRect) :
    Equiv.Perm {u : GmDart bb // GmInner bb u} :=
  ((gmdartMap bb).node).subtypePerm fun u => by
    simpa only [gmdartMap_node] using gmInner_gmnode_iff u

/-- The restricted node permutation acts as the node permutation. -/
@[simp] private theorem gmnodeInner_val (u : {u : GmDart bb // GmInner bb u}) :
    ((gmnodeInner bb u : {u : GmDart bb // GmInner bb u}) : GmDart bb)
      = (gmdartMap bb).node (u : GmDart bb) := rfl

/-- The inside of the box is a union of node orbits. -/
private theorem gmInner_cnode {u v : GmDart bb} (hu : GmInner bb u)
    (h : (gmdartMap bb).CNode u v) : GmInner bb v := by
  have hstep : ∀ z : GmDart bb,
      (fun w : GmDart bb => GmInner bb w) ((gmdartMap bb).node z)
        = (fun w : GmDart bb => GmInner bb w) z := by
    intro z
    exact propext (by simpa only [gmdartMap_node] using gmInner_gmnode_iff z)
  exact congr_of_sameCycle' (F := fun w : GmDart bb => GmInner bb w) hstep h ▸ hu

/-- The pixel of an inner dart is constant along its node orbit. -/
private theorem halfg_cnode {u v : GmDart bb} (hu : GmInner bb u)
    (h : (gmdartMap bb).CNode u v) : halfg v.1 = halfg u.1 := by
  have hv : GmInner bb v := gmInner_cnode hu h
  have hsc : (gmnodeInner bb).SameCycle ⟨u, hu⟩ ⟨v, hv⟩ :=
    Equiv.Perm.sameCycle_subtypePerm.mpr h
  have hstep : ∀ z : {u : GmDart bb // GmInner bb u},
      (fun w : {u : GmDart bb // GmInner bb u} => halfg (w : GmDart bb).1) (gmnodeInner bb z)
        = (fun w : {u : GmDart bb // GmInner bb u} => halfg (w : GmDart bb).1) z := by
    intro z
    simp only [gmnodeInner_val, gmdartMap_node, gmnode_val_of_inner z.2, halfg_gedge_gnode]
  exact (congr_of_sameCycle'
    (F := fun w : {u : GmDart bb // GmInner bb u} => halfg (w : GmDart bb).1) hstep hsc).symm

/-- **A lower bound for the node count of the box map**: the four darts of a
pixel form a node orbit, so there is at least one node per pixel. -/
theorem fcard_gmnode : bb.area ≤ cycleCount (gmdartMap bb).node := by
  classical
  have hmem : ∀ p : {p : GPoint // p ∈ bb.toFinset}, (p : GPoint) + p ∈ gmgrid bb := fun p =>
    mem_gmgrid.mpr (Or.inl (by rw [halfg_double]; exact (GRect.mem_toFinset _ _).mp p.2))
  have hinner : ∀ p : {p : GPoint // p ∈ bb.toFinset},
      GmInner bb (⟨(p : GPoint) + p, hmem p⟩ : GmDart bb) := by
    intro p
    change halfg ((p : GPoint) + p) ∈ bb.toRegion
    rw [halfg_double]
    exact (GRect.mem_toFinset _ _).mp p.2
  have hinj : Function.Injective (fun p : {p : GPoint // p ∈ bb.toFinset} =>
      Quotient.mk (Equiv.Perm.SameCycle.setoid (gmdartMap bb).node)
        (⟨(p : GPoint) + p, hmem p⟩ : GmDart bb)) := by
    intro p q hpq
    have hsc : (gmdartMap bb).CNode (⟨(p : GPoint) + p, hmem p⟩ : GmDart bb)
        ⟨(q : GPoint) + q, hmem q⟩ := Quotient.exact hpq
    have hh := halfg_cnode (hinner p) hsc
    rw [halfg_double, halfg_double] at hh
    exact Subtype.ext hh.symm
  have hle := Nat.card_le_card_of_injective _ hinj
  have hc : Nat.card {p : GPoint // p ∈ bb.toFinset} = bb.area := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, GRect.card_toFinset]
  rwa [hc] at hle


/-! ### Connectivity of the box map

Every dart is linked to the dart `(p₀, p₀)` at the lower left corner of the
box: an edge link reaches the inside from the frame, node links join the four
darts of a pixel, and an edge link then moves to the neighbouring pixel.
-/

/-- A dart is determined by its pixel and its parity. -/
private theorem eq_of_halfg_oddg {d e : GPoint} (h1 : halfg d = halfg e) (h2 : oddg d = oddg e) :
    d = e :=
  calc d = halfg d + halfg d + oddg d := (halfgK d).symm
    _ = halfg e + halfg e + oddg e := by rw [h1, h2]
    _ = e := halfgK e

/-- The node permutation turns an inner dart by three quarters. -/
private theorem oddg_gmnode_of_inner {w : GmDart bb} (h : GmInner bb w) :
    oddg (gmnode w).1 = ccw (ccw (ccw (oddg w.1))) := by
  rw [gmnode_val_of_inner h, oddg_gedge, oddg_gnode]

/-- The four darts of an inner pixel are joined by node links. -/
private theorem inner_pixel_darts {w : GmDart bb} (hw : GmInner bb w) (v : GmDart bb)
    (hv : halfg v.1 = halfg w.1) : Relation.EqvGen (gmdartMap bb).GLink w v := by
  have hstep : ∀ z : GmDart bb, Relation.EqvGen (gmdartMap bb).GLink z (gmnode z) := fun z =>
    Relation.EqvGen.rel _ _ (Or.inr (Or.inl (gmdartMap_node z).symm))
  have h1 : GmInner bb (gmnode w) := gmInner_gmnode hw
  have h2 : GmInner bb (gmnode (gmnode w)) := gmInner_gmnode h1
  have p1 : halfg (gmnode w).1 = halfg w.1 := by
    rw [gmnode_val_of_inner hw, halfg_gedge_gnode]
  have p2 : halfg (gmnode (gmnode w)).1 = halfg w.1 := by
    rw [gmnode_val_of_inner h1, halfg_gedge_gnode, p1]
  have p3 : halfg (gmnode (gmnode (gmnode w))).1 = halfg w.1 := by
    rw [gmnode_val_of_inner h2, halfg_gedge_gnode, p2]
  have o1 : oddg (gmnode w).1 = ccw (ccw (ccw (oddg w.1))) := oddg_gmnode_of_inner hw
  have o2 : oddg (gmnode (gmnode w)).1 = ccw (ccw (oddg w.1)) := by
    rw [oddg_gmnode_of_inner h1, o1]; simp only [ccw4]
  have o3 : oddg (gmnode (gmnode (gmnode w))).1 = ccw (oddg w.1) := by
    rw [oddg_gmnode_of_inner h2, o2]; simp only [ccw4]
  obtain ⟨i, hi, hci⟩ := exists_iter_ccw (oddgP w.1) (oddgP v.1)
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi4 with rfl | rfl | rfl | rfl <;>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hci
  · rw [← show w = v from Subtype.ext (eq_of_halfg_oddg hv.symm hci)]
    exact Relation.EqvGen.refl w
  · rw [← show gmnode (gmnode (gmnode w)) = v from
      Subtype.ext (eq_of_halfg_oddg (p3.trans hv.symm) (o3.trans hci))]
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (hstep w) (hstep (gmnode w)))
      (hstep (gmnode (gmnode w)))
  · rw [← show gmnode (gmnode w) = v from
      Subtype.ext (eq_of_halfg_oddg (p2.trans hv.symm) (o2.trans hci))]
    exact Relation.EqvGen.trans _ _ _ (hstep w) (hstep (gmnode w))
  · rw [← show gmnode w = v from
      Subtype.ext (eq_of_halfg_oddg (p1.trans hv.symm) (o1.trans hci))]
    exact hstep w

/-- From an inner dart one reaches, by node and edge links, an inner dart of
the neighbouring pixel in any direction that stays inside the box. -/
private theorem eqvGen_glink_step {v : GmDart bb} (hv : GmInner bb v) {c : GPoint}
    (hc : IsOddg c) (hq : halfg v.1 + gdir c ∈ bb.toRegion) :
    ∃ w : GmDart bb, GmInner bb w ∧ halfg w.1 = halfg v.1 + gdir c ∧
      Relation.EqvGen (gmdartMap bb).GLink v w := by
  have hd : halfg v.1 + halfg v.1 + c ∈ gmgrid bb :=
    mem_gmgrid.mpr (Or.inl (by rw [halfg_eq hc]; exact hv))
  have hzp : halfg (⟨halfg v.1 + halfg v.1 + c, hd⟩ : GmDart bb).1 = halfg v.1 := halfg_eq hc
  have hzin : GmInner bb (⟨halfg v.1 + halfg v.1 + c, hd⟩ : GmDart bb) := by
    have : halfg (halfg v.1 + halfg v.1 + c) ∈ bb.toRegion := by rw [halfg_eq hc]; exact hv
    exact this
  have hvz : Relation.EqvGen (gmdartMap bb).GLink v ⟨halfg v.1 + halfg v.1 + c, hd⟩ :=
    inner_pixel_darts hv _ hzp
  have hew : halfg (gmedge (⟨halfg v.1 + halfg v.1 + c, hd⟩ : GmDart bb)).1
      = halfg v.1 + gdir c := by
    have : halfg (gedge (halfg v.1 + halfg v.1 + c)) = halfg v.1 + gdir c := by
      rw [halfg_gedge_gdir, halfg_eq hc, oddg_eq hc]
    exact this
  refine ⟨gmedge ⟨halfg v.1 + halfg v.1 + c, hd⟩, ?_, hew, ?_⟩
  · have : halfg (gmedge (⟨halfg v.1 + halfg v.1 + c, hd⟩ : GmDart bb)).1 ∈ bb.toRegion := by
      rw [hew]; exact hq
    exact this
  · exact Relation.EqvGen.trans _ _ _ hvz
      (Relation.EqvGen.rel _ _ (Or.inl (gmdartMap_edge _).symm))

/-- A hypermap all of whose darts are linked to one fixed dart is connected. -/
private theorem connected_of_forall_eqvGen {D : Type*} [Finite D] (H : Hypermap D) (z : D)
    (h : ∀ u : D, Relation.EqvGen H.GLink u z) : H.Connected := by
  have hcard : Nat.card (Quotient H.gcompSetoid) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨?_⟩, ⟨Quotient.mk H.gcompSetoid z⟩⟩
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound (Relation.EqvGen.trans _ _ _ (h a)
      (Relation.EqvGen.symm _ _ (h b)))
  exact hcard

/-- **The box map is connected.** -/
theorem gmdart_connected (hbb : bb.Proper) : (gmdartMap bb).Connected := by
  obtain ⟨hx, hy⟩ := (GRect.proper_iff bb).mp hbb
  have hp0bb : ((bb.xmin, bb.ymin) : GPoint) ∈ bb.toRegion := ⟨le_rfl, hx, le_rfl, hy⟩
  have hu0 : ((bb.xmin, bb.ymin) : GPoint) + (bb.xmin, bb.ymin) ∈ gmgrid bb :=
    mem_gmgrid.mpr (Or.inl (by rw [halfg_double]; exact hp0bb))
  have hu0p : halfg ((⟨(bb.xmin, bb.ymin) + (bb.xmin, bb.ymin), hu0⟩ : GmDart bb)).1
      = ((bb.xmin, bb.ymin) : GPoint) := halfg_double _
  refine connected_of_forall_eqvGen _ ⟨(bb.xmin, bb.ymin) + (bb.xmin, bb.ymin), hu0⟩ ?_
  have key : ∀ n : ℕ, ∀ v : GmDart bb, GmInner bb v →
      ((halfg v.1).1 - bb.xmin).toNat + ((halfg v.1).2 - bb.ymin).toNat ≤ n →
      Relation.EqvGen (gmdartMap bb).GLink v
        ⟨(bb.xmin, bb.ymin) + (bb.xmin, bb.ymin), hu0⟩ := by
    intro n
    induction n with
    | zero =>
      intro v hv hn
      have hvb : halfg v.1 ∈ bb.toRegion := hv
      simp only [GRect.mem_toRegion] at hvb
      refine inner_pixel_darts hv _ ?_
      rw [hu0p]
      exact (Prod.ext (by omega) (by omega)).symm
    | succ n ih =>
      intro v hv hn
      have hvb : halfg v.1 ∈ bb.toRegion := hv
      simp only [GRect.mem_toRegion] at hvb
      by_cases hx0 : bb.xmin < (halfg v.1).1
      · obtain ⟨w, hw, hwp, hvw⟩ := eqvGen_glink_step hv (c := (0, 1))
          ⟨Or.inl rfl, Or.inr rfl⟩
          (by rw [gdir_01]; simp only [GRect.mem_toRegion, Prod.fst_add, Prod.snd_add]; omega)
        refine Relation.EqvGen.trans _ _ _ hvw (ih w hw ?_)
        rw [hwp, gdir_01]
        simp only [Prod.fst_add, Prod.snd_add]
        omega
      · by_cases hy0 : bb.ymin < (halfg v.1).2
        · obtain ⟨w, hw, hwp, hvw⟩ := eqvGen_glink_step hv (c := (0, 0))
            ⟨Or.inl rfl, Or.inl rfl⟩
            (by rw [gdir_00]; simp only [GRect.mem_toRegion, Prod.fst_add, Prod.snd_add]; omega)
          refine Relation.EqvGen.trans _ _ _ hvw (ih w hw ?_)
          rw [hwp, gdir_00]
          simp only [Prod.fst_add, Prod.snd_add]
          omega
        · refine inner_pixel_darts hv _ ?_
          rw [hu0p]
          exact (Prod.ext (by omega) (by omega)).symm
  intro u
  by_cases hu : GmInner bb u
  · exact key _ u hu le_rfl
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inl (gmdartMap_edge u).symm))
      (key _ (gmedge u) ((gmInner_or_gmInner_gmedge u).resolve_left hu) le_rfl)


/-! ### Planarity of the box map -/

/-- **The box map is planar.**  Euler's formula is an equality here: the dart
count and the three orbit counts computed above leave no genus. -/
theorem gmdart_planar (hbb : bb.Proper) : (gmdartMap bb).Planar := by
  have hconn : (gmdartMap bb).compCount = 1 := gmdart_connected hbb
  have hcard := card_gmdart hbb
  have hedge : Nat.card (GmDart bb) = 2 * cycleCount (gmdartMap bb).edge :=
    (plain_gmdartMap bb).card_eq
  have hnode : bb.width * bb.height ≤ cycleCount (gmdartMap bb).node := fcard_gmnode
  have hface : cycleCount (gmdartMap bb).face
      = bb.width * bb.height + bb.width + bb.height + 1 := by
    rw [fcard_gmface hbb]; ring
  simp only [Hypermap.Planar, Hypermap.genus, Hypermap.EulerLhs, Hypermap.EulerRhs, hconn]
  obtain ⟨A, hA⟩ : ∃ A, bb.width * bb.height = A := ⟨_, rfl⟩
  rw [hA] at hcard hnode hface
  omega


/-! ### The matte rings as rings of the box map

The bounding box contains every matte, so the contour of each matte is a list
of darts of the box map.  It is a face-simple `Rlink` cycle there, and the
disks it bounds are pairwise disjoint because the mattes are.
-/

section Rings

variable {cm : CMatte Nr}

/-- Every contour dart of a matte of the family is a dart of the box map. -/
theorem mem_gmgrid_of_mem_ring {i : Fin Nr} {d : GPoint} (hd : d ∈ (cm i).ring) :
    d ∈ gmgrid (cmBBox cm) :=
  mem_gmgrid.mpr (Or.inl (sub_cmBBox cm i (((cm i).mem_ring d).mp hd).1))

/-- The contour of the `i`-th matte, as a ring of darts of the box map. -/
noncomputable def gmring (cm : CMatte Nr) (i : Fin Nr) : List (GmDart (cmBBox cm)) :=
  (cm i).ring.pmap (fun d h => (⟨d, h⟩ : GmDart (cmBBox cm)))
    fun _ hd => mem_gmgrid_of_mem_ring hd

/-- `gmring` is the contour of the matte, read in the box map. -/
@[simp] theorem val_gmring (cm : CMatte Nr) (i : Fin Nr) :
    (gmring cm i).map Subtype.val = (cm i).ring := by
  rw [gmring, List.map_pmap]
  simp [List.pmap_eq_map]

theorem mem_gmring {i : Fin Nr} {u : GmDart (cmBBox cm)} :
    u ∈ gmring cm i ↔ u.1 ∈ (cm i).ring := by
  rw [← val_gmring cm i, List.mem_map]
  exact ⟨fun h => ⟨u, h, rfl⟩, fun ⟨v, hv, hvu⟩ => (Subtype.ext hvu : v = u) ▸ hv⟩

/-- Face-simplicity of a list of darts of the box map is duplicate-freeness of
its list of start vertices. -/
private theorem simple_iff_nodup_end0g {bb : GRect} (l : List (GmDart bb)) :
    (gmdartMap bb).Simple l ↔ (l.map fun u => end0g u.1).Nodup := by
  rw [Hypermap.Simple, List.Nodup, List.pairwise_map]
  constructor
  · exact fun h => h.imp fun {a b} hab hq => hab ((cface_end0g a b).mpr hq)
  · exact fun h => h.imp fun {a b} hab hc => hab ((cface_end0g a b).mp hc)

/-- The ring link of the box map is the contour link of the grid. -/
private theorem rlink_iff_mrlink {bb : GRect} (u v : GmDart bb) :
    (gmdartMap bb).Rlink u v ↔ MRLink u.1 v.1 := by
  rw [Hypermap.Rlink, cface_end0g, gmdartMap_edge, gmedge_val, end0g_gedge, MRLink]

/-- **The matte contours are face-simple ring cycles of the box map.** -/
theorem gmring_cycle (cm : CMatte Nr) (i : Fin Nr) :
    (gmdartMap (cmBBox cm)).Scycle (gmdartMap (cmBBox cm)).Rlink (gmring cm i) := by
  constructor
  · have hring := (isRingCycle_iff MRLink (cm i).ring).mp (cm i).ring_cycle
    rw [← val_gmring cm i] at hring
    obtain ⟨hchain, hwrap⟩ := hring
    constructor
    · rw [List.isChain_map] at hchain
      exact hchain.imp fun {a b} hab => (rlink_iff_mrlink a b).mpr hab
    · intro x hx z hz
      rw [rlink_iff_mrlink]
      refine hwrap x.1 ?_ z.1 ?_
      · rw [List.getLast?_map]; exact Option.mem_map_of_mem _ hx
      · rw [List.head?_map]; exact Option.mem_map_of_mem _ hz
  · rw [simple_iff_nodup_end0g]
    have hmap : ((gmring cm i).map fun u => end0g u.1) = (cm i).ring.map end0g := by
      rw [← val_gmring cm i, List.map_map]; rfl
    rw [hmap]
    exact (cm i).ring_simple

/-- If the node image of a dart is inner, so is the dart, and they share their
pixel. -/
private theorem inner_of_gmnode {bb : GRect} {b : GmDart bb} (h : GmInner bb (gmnode b)) :
    GmInner bb b ∧ halfg (gmnode b).1 = halfg b.1 := by
  have hb : GmInner bb b := (gmInner_gmnode_iff b).mp h
  exact ⟨hb, by rw [gmnode_val_of_inner hb, halfg_gedge_gnode]⟩

/-- **The disk bounded by a matte contour consists of darts of that matte.** -/
theorem gm_disk_def (cm : CMatte Nr) (i : Fin Nr) {u : GmDart (cmBBox cm)}
    (h : (gmdartMap (cmBBox cm)).DiskN (gmring cm i) u) : halfg u.1 ∈ (cm i).disk := by
  obtain ⟨y, hy, hpath⟩ := h
  have hydisk : halfg y.1 ∈ (cm i).disk := (((cm i).mem_ring y.1).mp (mem_gmring.mp hy)).1
  have hbase : halfg ((gmdartMap (cmBBox cm)).node⁻¹ y).1 ∈ (cm i).disk := by
    have hgn : gmnode ((gmdartMap (cmBBox cm)).node⁻¹ y) = y := by
      rw [← gmdartMap_node]; simp
    have hin : GmInner (cmBBox cm) (gmnode ((gmdartMap (cmBBox cm)).node⁻¹ y)) := by
      rw [hgn]; exact sub_cmBBox cm i hydisk
    obtain ⟨-, hh⟩ := inner_of_gmnode hin
    rw [hgn] at hh
    rw [← hh]; exact hydisk
  induction hpath with
  | refl => exact hbase
  | tail hbc hcd ih =>
    rename_i b c
    have hbdisk : halfg b.1 ∈ (cm i).disk := ih
    obtain ⟨hbr, hlink⟩ := hcd
    rcases hlink with hnb | hfb
    · -- `b` is the node of `c`
      have hin : GmInner (cmBBox cm) (gmnode c) := by
        have : gmnode c = b := by rw [← gmdartMap_node]; exact hnb.symm
        rw [this]
        exact sub_cmBBox cm i hbdisk
      obtain ⟨-, hh⟩ := inner_of_gmnode hin
      have hbc' : gmnode c = b := by rw [← gmdartMap_node]; exact hnb.symm
      rw [hbc'] at hh
      rw [← hh]; exact hbdisk
    · -- `c` is the face of `b`
      have hedge : halfg (gedge b.1) ∈ (cm i).disk := by
        by_contra hc
        exact hbr (mem_gmring.mpr (((cm i).mem_ring b.1).mpr ⟨hbdisk, hc⟩))
      have hnc : gmnode c = gmedge b := by
        have h1 : (gmdartMap (cmBBox cm)).edge ((gmdartMap (cmBBox cm)).node c) = b := by
          rw [← hfb]; exact (gmdartMap (cmBBox cm)).faceK b
        have h2 := congrArg (gmdartMap (cmBBox cm)).edge h1
        simp only [gmdartMap_edge, gmdartMap_node] at h2
        rw [← h2]
        exact (Subtype.ext (gedge2 _)).symm
      have hin : GmInner (cmBBox cm) (gmnode c) := by
        rw [hnc]
        exact sub_cmBBox cm i hedge
      obtain ⟨-, hh⟩ := inner_of_gmnode hin
      rw [hnc] at hh
      rw [← hh]
      exact hedge

/-- **The disks bounded by the matte contours are pairwise disjoint.** -/
theorem disjoint_gmdisk {cm : CMatte Nr} (hcm : CMProper cm) {i j : Fin Nr} (hij : i ≠ j)
    {u : GmDart (cmBBox cm)} (hi : (gmdartMap (cmBBox cm)).DiskN (gmring cm i) u)
    (hj : (gmdartMap (cmBBox cm)).DiskN (gmring cm j) u) : False :=
  hij (hcm i j ⟨halfg u.1, gm_disk_def cm i hi, gm_disk_def cm j hj⟩)

end Rings


/-! ### Cutting the matte disks out of the box map

Removing the interior of one matte contour at a time, using `Snip`, turns the
box map into a map in which every matte contour has become a node orbit.  A
`GmCutout cm E` records such a partial cut-out: the mattes indexed by `E` have
already been removed.
-/

section Cutout

variable {cm : CMatte Nr}

/-- A list is a cyclic chain for a weaker relation. -/
private theorem isCyclicChain_imp {α : Type*} {R S : α → α → Prop} (H : ∀ a b, R a b → S a b)
    {l : List α} (h : IsCyclicChain R l) : IsCyclicChain S l :=
  ⟨h.1.imp H, fun x hx y hy => H x y (h.2 x hx y hy)⟩

/-- A list is a cyclic chain for a relation that is only weakened on its own
elements. -/
private theorem isCyclicChain_imp_of_mem {α : Type*} {R S : α → α → Prop} {l : List α}
    (H : ∀ a ∈ l, ∀ b ∈ l, R a b → S a b) (h : IsCyclicChain R l) : IsCyclicChain S l :=
  ⟨h.1.imp_of_mem_imp fun a b ha hb => H a ha b hb,
    fun x hx y hy => H x (List.mem_of_mem_getLast? hx) y (List.mem_of_mem_head? hy)
      (h.2 x hx y hy)⟩

/-- Cyclic chains pull back along an arbitrary map. -/
private theorem isCyclicChain_of_map {α β : Type*} {R : β → β → Prop} {f : α → β} {l : List α}
    (h : IsCyclicChain R (l.map f)) : IsCyclicChain (fun a b => R (f a) (f b)) l := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨(List.isChain_map f).mp h1, fun x hx y hy => h2 (f x) ?_ (f y) ?_⟩
  · rw [List.getLast?_map]; exact Option.mem_map_of_mem _ hx
  · rw [List.head?_map]; exact Option.mem_map_of_mem _ hy

/-- A predicate on a finite type that is preserved by a permutation is
invariant under it. -/
private theorem perm_invariant_of_closed {D : Type*} [Finite D] {f : Equiv.Perm D}
    {P : D → Prop} (h : ∀ x, P x → P (f x)) (x : D) : P (f x) ↔ P x := by
  classical
  have _ : Fintype D := Fintype.ofFinite D
  refine ⟨fun hfx => ?_, h x⟩
  set I : Finset D := Finset.univ.filter P with hI
  have hmaps : I.image f ⊆ I := by
    intro v hv
    simp only [hI, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw
  have hcard : (I.image f).card = I.card := Finset.card_image_of_injective _ f.injective
  have heq : I.image f = I := Finset.eq_of_subset_of_card_le hmaps (le_of_eq hcard.symm)
  have hmemI : f x ∈ I := by
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfx
  rw [← heq, Finset.mem_image] at hmemI
  obtain ⟨w, hw, hwx⟩ := hmemI
  simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rwa [f.injective hwx] at hw

/-- A *cut-out* of the box map along the mattes indexed by `E`: a planar map
embedded in the box map by `emb`, preserving edges and faces everywhere and
nodes away from the rings, in which each already-removed matte contour has
become a node cycle. -/
structure GmCutout (cm : CMatte Nr) (E : Finset (Fin Nr)) : Type 1 where
  /-- The darts of the cut-out map. -/
  Dart : Type
  /-- Its darts have decidable equality. -/
  decEq : DecidableEq Dart
  /-- It has finitely many darts. -/
  fin : Finite Dart
  /-- The cut-out map. -/
  map : Hypermap Dart
  /-- The embedding into the box map. -/
  emb : Dart → GmDart (cmBBox cm)
  /-- The image of each matte contour. -/
  ring : Fin Nr → List Dart
  /-- The cut-out map is planar. -/
  planar : map.Planar
  /-- The embedding is injective. -/
  emb_injective : Function.Injective emb
  /-- The embedding preserves edges. -/
  emb_edge : ∀ x, emb (map.edge x) = (gmdartMap (cmBBox cm)).edge (emb x)
  /-- The embedding preserves and reflects faces. -/
  emb_cface : ∀ x y, (gmdartMap (cmBBox cm)).CFace (emb x) (emb y) ↔ map.CFace x y
  /-- Away from the removed rings the embedding preserves nodes. -/
  emb_node : ∀ x, (∀ i ∈ E, x ∉ ring i) →
    emb (map.node x) = (gmdartMap (cmBBox cm)).node (emb x)
  /-- The rings map onto the matte contours, reversed. -/
  ring_eq : ∀ i, ((ring i).map emb).reverse = gmring cm i
  /-- A removed ring is a node cycle. -/
  ring_cycle : ∀ i ∈ E, IsCyclicChain (fun a b => b = map.node a) (ring i)
  /-- A removed ring has no repetitions. -/
  ring_nodup : ∀ i ∈ E, (ring i).Nodup

/-- The box map itself, the cut-out that removes nothing. -/
noncomputable def gmCutoutNil (cm : CMatte Nr) : GmCutout cm ∅ where
  Dart := GmDart (cmBBox cm)
  decEq := inferInstance
  fin := inferInstance
  map := gmdartMap (cmBBox cm)
  emb := id
  ring := fun i => (gmring cm i).reverse
  planar := gmdart_planar (cmBBox_proper cm)
  emb_injective := Function.injective_id
  emb_edge := fun _ => rfl
  emb_cface := fun _ _ => Iff.rfl
  emb_node := fun _ _ => rfl
  ring_eq := fun i => by simp
  ring_cycle := fun i hi => absurd hi (by simp)
  ring_nodup := fun i hi => absurd hi (by simp)

/-- **The inductive step**: one more matte disk is cut out of a cut-out.  The
`j`-th matte contour, reversed, is a face-simple ring cycle of the cut-out map,
so `Snip` removes its interior; in the remaining map that contour has become a
node cycle. -/
noncomputable def gmCutoutStep (hcm : CMProper cm) {E : Finset (Fin Nr)} {j : Fin Nr}
    (hj : j ∈ E) (C : GmCutout cm (E.erase j)) : GmCutout cm E := by
  haveI := C.decEq
  haveI := C.fin
  have hplanGM : (gmdartMap (cmBBox cm)).Planar := gmdart_planar (cmBBox_proper cm)
  have h_ring : ∀ (i : Fin Nr) (x : C.Dart), C.emb x ∈ gmring cm i ↔ x ∈ C.ring i := by
    intro i x
    rw [← C.ring_eq i, List.mem_reverse, List.mem_map]
    exact ⟨fun ⟨_, hy, hxy⟩ => C.emb_injective hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have h_rlink : ∀ a b : C.Dart,
      (gmdartMap (cmBBox cm)).Rlink (C.emb a) (C.emb b) ↔ C.map.Rlink a b := by
    intro a b
    rw [Hypermap.Rlink, Hypermap.Rlink, ← C.emb_edge, C.emb_cface]
  -- The reversed `j`-th ring is a face-simple ring cycle of the cut-out map.
  have hscyc : C.map.Scycle C.map.Rlink ((C.ring j).reverse) := by
    obtain ⟨hcyc, hsimp⟩ := gmring_cycle cm j
    rw [← C.ring_eq j] at hcyc hsimp
    have hmr : ((C.ring j).map C.emb).reverse = ((C.ring j).reverse).map C.emb := by simp
    rw [hmr] at hcyc hsimp
    exact ⟨isCyclicChain_imp (fun a b hab => (h_rlink a b).mp hab) (isCyclicChain_of_map hcyc),
      (Hypermap.simple_map (G := C.map) (fun x y => C.emb_cface x y) _).mp hsimp⟩
  -- The darts lying over the disk of the `j`-th matte.
  have hMj_not_ring : ∀ (i : Fin Nr), i ≠ j → ∀ x : C.Dart,
      (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb x) → x ∉ C.ring i := by
    intro i hij x hx hxi
    exact disjoint_gmdisk hcm hij (Hypermap.diskN_of_mem ((h_ring i x).mpr hxi)) hx
  have hMj_node : ∀ x : C.Dart, (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb x) →
      C.emb (C.map.node x) = (gmdartMap (cmBBox cm)).node (C.emb x) := fun x hx =>
    C.emb_node x fun i hi => hMj_not_ring i (Finset.ne_of_mem_erase hi) x hx
  have hMj_closed : ∀ x : C.Dart, (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb x) →
      (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb (C.map.node x)) := by
    intro x hx
    rw [hMj_node x hx]
    exact Hypermap.diskN_node hx
  have hMj_iff : ∀ x : C.Dart,
      (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb (C.map.node x)) ↔
        (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb x) :=
    fun x => perm_invariant_of_closed (f := C.map.node)
      (P := fun y => (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb y)) hMj_closed x
  -- The disk of the reversed ring lies over the disk of the matte.
  have h_mj : ∀ x : C.Dart, C.map.DiskN ((C.ring j).reverse) x →
      (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb x) := by
    intro x hx
    obtain ⟨z, hz, hpath⟩ := hx
    have hzM : (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb z) :=
      Hypermap.diskN_of_mem ((h_ring j z).mpr (List.mem_reverse.mp hz))
    have hbase : (gmdartMap (cmBBox cm)).DiskN (gmring cm j) (C.emb (C.map.node⁻¹ z)) := by
      rw [← hMj_iff (C.map.node⁻¹ z)]
      simpa using hzM
    induction hpath with
    | refl => exact hbase
    | tail hbc hcd ih =>
      rename_i b c
      obtain ⟨hbr, hlink⟩ := hcd
      rcases hlink with hnb | hfb
      · rw [← hMj_iff c, ← hnb]; exact ih
      · rw [← hMj_iff c]
        have hbDiskE : (gmdartMap (cmBBox cm)).DiskE (gmring cm j) (C.emb b) :=
          ⟨ih, fun hc => hbr (List.mem_reverse.mpr ((h_ring j b).mp hc))⟩
        have hkey : C.map.edge (C.map.node c) = b := by rw [← hfb]; exact C.map.faceK b
        have hE2 : (gmdartMap (cmBBox cm)).DiskE (gmring cm j)
            ((gmdartMap (cmBBox cm)).edge (C.emb (C.map.node c))) := by
          rw [← C.emb_edge, hkey]; exact hbDiskE
        exact ((Hypermap.diskE_edge_iff hplanGM (gmring_cycle cm j)).mp hE2).1
  -- Every ring dart survives the cut.
  have hnotDiskE : ∀ (i : Fin Nr), ∀ x ∈ C.ring i, ¬ C.map.DiskE ((C.ring j).reverse) x := by
    intro i x hx hD
    by_cases hij : i = j
    · exact hD.2 (List.mem_reverse.mpr (hij ▸ hx))
    · exact hMj_not_ring i hij x (h_mj x hD.1) hx
  set rj : Fin Nr → List {x : C.Dart // ¬ C.map.DiskE ((C.ring j).reverse) x} := fun i =>
    (C.ring i).pmap (fun x hx => (⟨x, hx⟩ :
      {x : C.Dart // ¬ C.map.DiskE ((C.ring j).reverse) x})) (fun x hx => hnotDiskE i x hx)
    with hrjdef
  have hrj : ∀ i, (rj i).map Subtype.val = C.ring i := by
    intro i
    rw [hrjdef, List.map_pmap]
    simp
  have h_rj : ∀ (i : Fin Nr) (x : {x : C.Dart // ¬ C.map.DiskE ((C.ring j).reverse) x}),
      x ∈ rj i ↔ x.1 ∈ C.ring i := by
    intro i x
    rw [← hrj i, List.mem_map]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨_, hy, hyx⟩ => (Subtype.ext hyx : _ = x) ▸ hy⟩
  have hrjj : rj j = C.map.sniprRing ((C.ring j).reverse) := by
    refine List.map_injective_iff.mpr (fun a b hab => Subtype.ext hab) ?_
    rw [hrj j]
    have hms := Hypermap.map_sniprRing (G := C.map) (r := (C.ring j).reverse)
    rw [List.reverse_reverse] at hms
    exact hms.symm
  have hnotring : ∀ (i : Fin Nr), i ≠ j → ∀ x ∈ rj i,
      x ∉ C.map.sniprRing ((C.ring j).reverse) := by
    intro i hij x hx hc
    exact hMj_not_ring i hij x.1
      (h_mj x.1 (Hypermap.diskN_of_mem (Hypermap.mem_sniprRing.mp hc))) ((h_rj i x).mp hx)
  have hpatch := Hypermap.snip_patch (G := C.map) (r := (C.ring j).reverse) C.planar hscyc
  exact
    { Dart := {x : C.Dart // ¬ C.map.DiskE ((C.ring j).reverse) x}
      decEq := inferInstance
      fin := inferInstance
      map := Hypermap.snipRem C.map ((C.ring j).reverse) C.planar hscyc
      emb := fun x => C.emb x.1
      ring := rj
      planar := Hypermap.planar_snipRem C.planar hscyc
      emb_injective := fun _ _ hab => Subtype.ext (C.emb_injective hab)
      emb_edge := by
        intro x
        rw [Hypermap.snipRem_edge]
        exact C.emb_edge x.1
      emb_cface := by
        intro x y
        rw [C.emb_cface]
        exact (hpatch.cface_hr_iff x y).symm
      emb_node := by
        intro x hx
        have hxr : x ∉ C.map.sniprRing ((C.ring j).reverse) := by
          rw [← hrjj]; exact hx j hj
        have h1 : ((Hypermap.snipRem C.map ((C.ring j).reverse) C.planar hscyc).node x).1
            = C.map.node x.1 := hpatch.node_r hxr
        rw [h1]
        refine C.emb_node x.1 fun i hi hc => ?_
        exact hx i (Finset.mem_of_mem_erase hi) ((h_rj i x).mpr hc)
      ring_eq := by
        intro i
        have hmi : (rj i).map (fun x => C.emb x.1) = (C.ring i).map C.emb := by
          rw [← hrj i, List.map_map]; rfl
        rw [hmi]
        exact C.ring_eq i
      ring_cycle := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          rw [hrjj]
          exact Hypermap.isCyclicChain_sniprRing C.planar hscyc
        · have hcy := C.ring_cycle i (Finset.mem_erase.mpr ⟨hij, hi⟩)
          rw [← hrj i] at hcy
          refine isCyclicChain_imp_of_mem (fun a ha b _ hab => ?_) (isCyclicChain_of_map hcy)
          have h1 : ((Hypermap.snipRem C.map ((C.ring j).reverse) C.planar hscyc).node a).1
              = C.map.node a.1 := hpatch.node_r (hnotring i hij a ha)
          exact Subtype.ext (hab.trans h1.symm)
      ring_nodup := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          rw [hrjj]
          exact Hypermap.nodup_sniprRing hscyc
        · refine List.Nodup.of_map Subtype.val ?_
          rw [hrj i]
          exact C.ring_nodup i (Finset.mem_erase.mpr ⟨hij, hi⟩) }

/-- A dart of a cut-out lies on the image of a matte contour exactly when its
embedding lies on that contour. -/
theorem GmCutout.mem_ring {E : Finset (Fin Nr)} (C : GmCutout cm E) (i : Fin Nr) (x : C.Dart) :
    C.emb x ∈ gmring cm i ↔ x ∈ C.ring i := by
  rw [← C.ring_eq i, List.mem_reverse, List.mem_map]
  exact ⟨fun ⟨_, hy, hxy⟩ => C.emb_injective hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private theorem has_cutout_aux (hcm : CMProper cm) :
    ∀ (n : ℕ) (E : Finset (Fin Nr)), E.card ≤ n → Nonempty (GmCutout cm E) := by
  intro n
  induction n with
  | zero =>
    intro E hE
    have hEe : E = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hE)
    subst hEe
    exact ⟨gmCutoutNil cm⟩
  | succ n ih =>
    intro E hE
    rcases E.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · exact ⟨gmCutoutNil cm⟩
    · have hpos : 0 < E.card := Finset.card_pos.mpr ⟨j, hj⟩
      have hcard : (E.erase j).card ≤ n := by
        have := Finset.card_erase_of_mem hj
        omega
      obtain ⟨C⟩ := ih (E.erase j) hcard
      exact ⟨gmCutoutStep hcm hj C⟩

/-- **Every matte disk can be cut out of the box map.** -/
theorem has_cutout (hcm : CMProper cm) : Nonempty (GmCutout cm Finset.univ) :=
  has_cutout_aux hcm _ _ le_rfl

/-- The full cut-out: the box map with the interior of every matte removed. -/
noncomputable def gridCutout (hcm : CMProper cm) : GmCutout cm Finset.univ :=
  Classical.choice (has_cutout hcm)

/-- **The grid map**: the dual of the fully cut-out map.  Its nodes are the
matte regions, so colouring its faces colours the regions. -/
noncomputable def gridMap (hcm : CMProper cm) : Hypermap (gridCutout hcm).Dart :=
  (gridCutout hcm).map.dual

theorem gridMap_eq (hcm : CMProper cm) : gridMap hcm = (gridCutout hcm).map.dual := rfl

/-- **The fully cut-out map is loopless**: no node contains both ends of an
edge.  On a contour that is now a node orbit this is the fact that a matte
contour never contains a dart together with its reverse; elsewhere it is the
fact that a dart and its reverse lie in different pixels. -/
theorem GmCutout.loopless (C : GmCutout cm Finset.univ) : C.map.Loopless := by
  have := C.decEq
  have := C.fin
  have hmain : ∀ x : C.Dart, GmInner (cmBBox cm) (C.emb x) →
      ¬ C.map.CNode x (C.map.edge x) := by
    intro x hin hcn
    by_cases hring : ∃ i, x ∈ C.ring i
    · obtain ⟨i, hi⟩ := hring
      have hcyc := C.ring_cycle i (Finset.mem_univ i)
      have hex : C.map.edge x ∈ C.ring i := (Hypermap.cnode_iff_mem hcyc hi _).mp hcn
      have h1 : (C.emb x).1 ∈ (cm i).ring := mem_gmring.mp ((C.mem_ring i x).mpr hi)
      have h4 : (C.emb (C.map.edge x)).1 = gedge (C.emb x).1 := by
        rw [C.emb_edge, gmdartMap_edge, gmedge_val]
      have h2 : gedge (C.emb x).1 ∈ (cm i).ring := by
        rw [← h4]
        exact mem_gmring.mp ((C.mem_ring i _).mpr hex)
      exact (cm i).gedge_notMem_ring h1 h2
    · push Not at hring
      have hstep : ∀ y : C.Dart, GmInner (cmBBox cm) (C.emb y) → (∀ i, y ∉ C.ring i) →
          GmInner (cmBBox cm) (C.emb (C.map.node y)) ∧ (∀ i, C.map.node y ∉ C.ring i) ∧
            halfg (C.emb (C.map.node y)).1 = halfg (C.emb y).1 := by
        intro y hiny hoff
        have hn : C.emb (C.map.node y) = (gmdartMap (cmBBox cm)).node (C.emb y) :=
          C.emb_node y fun i _ => hoff i
        refine ⟨by rw [hn, gmdartMap_node]; exact gmInner_gmnode hiny, ?_, ?_⟩
        · intro i hc
          exact hoff i
            ((Hypermap.node_mem_iff_mem (C.ring_cycle i (Finset.mem_univ i)) y).mp hc)
        · rw [hn, gmdartMap_node, gmnode_val_of_inner hiny, halfg_gedge_gnode]
      have hiter : ∀ (k : ℕ) (y : C.Dart), GmInner (cmBBox cm) (C.emb y) →
          (∀ i, y ∉ C.ring i) → halfg (C.emb (C.map.node^[k] y)).1 = halfg (C.emb y).1 := by
        intro k
        induction k with
        | zero => intro y _ _; rfl
        | succ k ih =>
          intro y hiny hoff
          rw [Function.iterate_succ_apply]
          obtain ⟨h1, h2, h3⟩ := hstep y hiny hoff
          rw [ih (C.map.node y) h1 h2, h3]
      obtain ⟨k, hk⟩ := hcn.exists_nat_pow_eq
      rw [Equiv.Perm.coe_pow] at hk
      have hfin := hiter k x hin hring
      rw [hk, C.emb_edge, gmdartMap_edge, gmedge_val] at hfin
      exact halfg_gedge_ne _ hfin
  intro x hx
  by_cases hin : GmInner (cmBBox cm) (C.emb x)
  · exact hmain x hin hx
  · have hin2 : GmInner (cmBBox cm) (C.emb (C.map.edge x)) := by
      rw [C.emb_edge]
      exact (gmInner_or_gmInner_gmedge (C.emb x)).resolve_left hin
    have hee : C.map.edge (C.map.edge x) = x := by
      apply C.emb_injective
      rw [C.emb_edge, C.emb_edge, gmdartMap_edge, gmdartMap_edge]
      exact Subtype.ext (gedge2 _)
    exact hmain (C.map.edge x) hin2 (by rw [hee]; exact hx.symm)

/-- **The grid map is planar and bridgeless.** -/
theorem planar_bridgeless_grid_map (hcm : CMProper cm) :
    (gridMap hcm).Planar ∧ (gridMap hcm).Bridgeless := by
  constructor
  · rw [gridMap_eq, Hypermap.planar_dual]
    exact (gridCutout hcm).planar
  · rw [gridMap_eq, Hypermap.bridgeless_dual]
    exact (gridCutout hcm).loopless

/-- **A four-colouring of the cut-out map's dual colours the mattes**: adjacent
mattes get different colours. -/
theorem GmCutout.coloring (C : GmCutout cm Finset.univ) (h : C.map.dual.FourColorable) :
    ∃ k : Fin Nr → Color, ∀ i j : Fin Nr, Matte.Adj (cm i) (cm j) → k i ≠ k j := by
  have := C.decEq
  have := C.fin
  obtain ⟨k, hk⟩ := Hypermap.fourColorable_dual_iff.mp h
  have knode : ∀ x y : C.Dart, C.map.CNode x y → k x = k y := fun x y hxy =>
    congr_of_sameCycle' (F := k) (fun z => hk.node z) hxy
  have hconst : ∀ (i : Fin Nr) (x : C.Dart), x ∈ C.ring i →
      ((C.ring i).head?).elim Color.c0 k = k x := by
    intro i x hx
    obtain ⟨a, ha⟩ : ∃ a, (C.ring i).head? = some a := by
      cases hl : C.ring i with
      | nil => rw [hl] at hx; exact absurd hx (List.not_mem_nil)
      | cons b t => exact ⟨b, rfl⟩
    rw [ha]
    exact knode a x ((Hypermap.cnode_iff_mem (C.ring_cycle i (Finset.mem_univ i))
      (List.mem_of_mem_head? ha) x).mpr hx)
  refine ⟨fun i => ((C.ring i).head?).elim Color.c0 k, fun i j hadj => ?_⟩
  obtain ⟨d, hdj, hdi⟩ := hadj
  have hdmem : d ∈ gmgrid (cmBBox cm) := mem_gmgrid_of_mem_ring hdj
  have hu : (⟨d, hdmem⟩ : GmDart (cmBBox cm)) ∈ gmring cm j := mem_gmring.mpr hdj
  rw [← C.ring_eq j, List.mem_reverse, List.mem_map] at hu
  obtain ⟨x, hxj, hxd⟩ := hu
  have hei : C.map.edge x ∈ C.ring i := by
    refine (C.mem_ring i _).mp (mem_gmring.mpr ?_)
    have hval : (C.emb (C.map.edge x)).1 = gedge d := by
      rw [C.emb_edge, gmdartMap_edge, gmedge_val, hxd]
    rw [hval]
    exact hdi
  simp only
  rw [hconst i _ hei, hconst j _ hxj]
  exact hk.edge x

/-- **The grid map colouring theorem.**  A four-colouring of the grid map
yields a colouring of the matte regions in which adjacent mattes get different
colours. -/
theorem grid_map_coloring (hcm : CMProper cm) (h : (gridMap hcm).FourColorable) :
    ∃ k : Fin Nr → Color, ∀ i j : Fin Nr, Matte.Adj (cm i) (cm j) → k i ≠ k j :=
  (gridCutout hcm).coloring h

/-- **The grid map of a well-formed adjacency pattern.**  From a family of
adjacency boxes and a family of disjoint mattes satisfying the three
well-formedness conditions one builds a planar bridgeless hypermap whose
four-colourings yield colourings of the prescribed adjacency pattern.  This is
the interface used by the discretisation step. -/
theorem exists_grid_map {ab0 : AdjBox Nr} {cm0 : CMatte Nr} (hab0 : ABProper ab0)
    (hcm0 : CMProper cm0) (habcm0 : ∀ e i, ABCMProper ab0 cm0 e i) :
    ∃ (D : Type) (_ : Finite D) (G : Hypermap D), G.Planar ∧ G.Bridgeless ∧
      (G.FourColorable → ∃ k : Fin Nr → Color, ∀ e : AdjIndex Nr,
        (ab0 e).Proper → k e.fst ≠ k e.snd) := by
  obtain ⟨cm, hcm, hadj⟩ := cm_extend_adj hab0 hcm0 habcm0
  refine ⟨(gridCutout hcm).Dart, (gridCutout hcm).fin, gridMap hcm,
    (planar_bridgeless_grid_map hcm).1, (planar_bridgeless_grid_map hcm).2, fun h => ?_⟩
  obtain ⟨k, hk⟩ := grid_map_coloring hcm h
  exact ⟨k, fun e he => hk e.fst e.snd (hadj e he)⟩

end Cutout

end FourColor

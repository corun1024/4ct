import FourColor.Geometry
import FourColor.Jordan
import FourColor.Orbit
import FourColor.Patch

/-!
# Cutting a map along a ring: the snip construction

A simple ring of a hypermap delimits a disk: the darts reachable from the ring
by a contour path that starts with a reverse N-link and stays off the ring on
the way.  This file defines that disk and its edge-, face- and
complement-closed variants, and then cuts a planar map along the ring into a
*disk* map and a *remainder* map that form a `Patch`.

The interior of the disk is edge-closed, and that is the only statement here
that needs planarity: an edge leaving the interior would close up a Moebius
contour running around the ring, which `Hypermap.Planar.jordan` forbids.  The
contour is built inside the proof, from the face chains joining consecutive
ring darts.

## Main definitions

* `Hypermap.DLink` — a contour link out of a dart off the ring.
* `Hypermap.DConnect` — an internally ring-disjoint contour path.
* `Hypermap.DiskN`, `DiskE`, `DiskF`, `DiskFC` — the disk and its variants.
* `Hypermap.RClink` — the contour successor used to cut along the ring.
* `Hypermap.snipDisk`, `Hypermap.snipd`, `Hypermap.snipdRing` — the disk map,
  its projection into `G`, and its border E-cycle.
* `Hypermap.snipRem`, `Hypermap.snipr`, `Hypermap.sniprRing` — the remainder
  map, its projection into `G`, and its border N-cycle.

## Main results

* `Hypermap.diskN_node` — the disk is closed under `node`.
* `Hypermap.diskN_iff` — it is the ring together with its edge interior.
* `Hypermap.diskF_face_iff`, `Hypermap.diskFC_face_iff` — the face-closed
  variants are closed under `face`.
* `Hypermap.diskE_edge` — the interior of the disk is closed under `edge`.
* `Hypermap.scycle_snipdRing`, `Hypermap.isCyclicChain_sniprRing` — the two
  border rings.
* `Hypermap.snip_patch` — the two maps patch back together into `G`, and hence
  `Hypermap.planar_snipDisk`, `Hypermap.planar_snipRem`.
-/

namespace FourColor

namespace Hypermap

open Equiv Equiv.Perm

variable {D : Type*} (G : Hypermap D) (r : List D)

/-- A contour link out of a dart that is not on the ring. -/
def DLink (x y : D) : Prop := x ∉ r ∧ G.Clink x y

/-- `DConnect r x y`: there is a contour path from `y` to `x` that starts with a
reverse N-link and stays off the ring on the way. -/
def DConnect (x y : D) : Prop :=
  Relation.ReflTransGen (G.DLink r) (G.node⁻¹ y) x

/-- The disk delimited by the ring: the darts connected to it from inside. -/
def DiskN (x : D) : Prop := ∃ y ∈ r, G.DConnect r x y

/-- The disk with the ring removed. -/
def DiskE (x : D) : Prop := G.DiskN r x ∧ x ∉ r

/-- The disk with the whole face band of the ring removed. -/
def DiskF (x : D) : Prop := G.DiskN r x ∧ ¬ G.Fband r x

/-- Strictly outside the face closure of the disk. -/
def DiskFC (x : D) : Prop := ¬ G.DiskN r x ∧ ¬ G.Fband r x

variable {G r}

/-! ### Closure properties -/

/-- Stepping back along `node` stays in the disk. -/
theorem diskN_nodeInv {x : D} (h : G.DiskN r x) : G.DiskN r (G.node⁻¹ x) := by
  obtain ⟨y, hy, hpath⟩ := h
  by_cases hx : x ∈ r
  · exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  · exact ⟨y, hy, hpath.tail ⟨hx, Or.inl (by simp)⟩⟩

/-- Iterating a closure property of a permutation around its orbit. -/
private theorem closed_of_closed_inv [Finite D] {f : Perm D} {P : D → Prop}
    (h : ∀ x, P x → P (f⁻¹ x)) {x : D} (hx : P x) : P (f x) := by
  have hpow : ∀ n : ℕ, P (((f⁻¹) ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have hstep : ((f⁻¹) ^ (n + 1)) x = f⁻¹ (((f⁻¹) ^ n) x) := by
        rw [pow_succ']
        rfl
      rw [hstep]
      exact h _ ih
  have hpos : 0 < orderOf f := orderOf_pos f
  have hmul : f⁻¹ * (f⁻¹) ^ (orderOf f - 1) = 1 := by
    rw [← pow_succ', show orderOf f - 1 + 1 = orderOf f by omega, inv_pow,
      pow_orderOf_eq_one, inv_one]
  have hf : f = (f⁻¹) ^ (orderOf f - 1) := by
    have := inv_eq_of_mul_eq_one_right hmul
    rwa [inv_inv] at this
  rw [hf]
  exact hpow _

/-- The disk is closed under `node`. -/
theorem diskN_node [Finite D] {x : D} (h : G.DiskN r x) : G.DiskN r (G.node x) :=
  closed_of_closed_inv (f := G.node) (fun _ hz => diskN_nodeInv hz) h

/-- The ring lies in the disk. -/
theorem diskN_of_mem [Finite D] {x : D} (hx : x ∈ r) : G.DiskN r x := by
  have h : G.DiskN r (G.node⁻¹ x) := ⟨x, hx, Relation.ReflTransGen.refl⟩
  have h2 := diskN_node h
  simpa using h2

/-- The disk is the ring together with its interior. -/
theorem diskN_iff [Finite D] {x : D} : G.DiskN r x ↔ x ∈ r ∨ G.DiskE r x := by
  constructor
  · intro h
    by_cases hx : x ∈ r
    · exact Or.inl hx
    · exact Or.inr ⟨h, hx⟩
  · rintro (hx | ⟨h, -⟩)
    · exact diskN_of_mem hx
    · exact h

/-- Stepping forward along `face` stays in the face-closed disk. -/
theorem diskF_faceStep {x : D} (h : G.DiskF r x) : G.DiskF r (G.face x) := by
  obtain ⟨⟨y, hy, hpath⟩, hband⟩ := h
  have hxr : x ∉ r := fun hc => hband (G.fband_of_mem hc)
  refine ⟨⟨y, hy, hpath.tail ⟨hxr, Or.inr rfl⟩⟩, ?_⟩
  rwa [G.fband_face]

/-- The face-closed disk is closed under `face`. -/
theorem diskF_faceInv [Finite D] {x : D} (h : G.DiskF r x) : G.DiskF r (G.face⁻¹ x) := by
  refine closed_of_closed_inv (f := G.face⁻¹) (fun z hz => ?_) h
  rw [inv_inv]
  exact diskF_faceStep hz

/-- The complement of the face closure of the disk is closed under `face`. -/
theorem diskFC_faceStep [Finite D] {x : D} (h : G.DiskFC r x) : G.DiskFC r (G.face x) := by
  obtain ⟨hN, hband⟩ := h
  have hband' : ¬ G.Fband r (G.face x) := by rwa [G.fband_face]
  refine ⟨fun hc => hN ?_, hband'⟩
  have hF : G.DiskF r (G.face x) := ⟨hc, hband'⟩
  have hx : G.DiskF r (G.face⁻¹ (G.face x)) := diskF_faceInv hF
  simpa using hx.1


/-- The complement of the face closure of the disk is closed under `face`
backwards. -/
theorem diskFC_faceInv [Finite D] {x : D} (h : G.DiskFC r x) : G.DiskFC r (G.face⁻¹ x) := by
  refine closed_of_closed_inv (f := G.face⁻¹) (fun z hz => ?_) h
  rw [inv_inv]
  exact diskFC_faceStep hz

/-- The disk is invariant along node orbits. -/
theorem diskN_node_iff [Finite D] {x : D} : G.DiskN r (G.node x) ↔ G.DiskN r x := by
  refine ⟨fun h => ?_, diskN_node⟩
  simpa using diskN_nodeInv h

/-- The face-closed disk is invariant along face orbits. -/
theorem diskF_face_iff [Finite D] {x : D} : G.DiskF r (G.face x) ↔ G.DiskF r x :=
  ⟨fun h => by simpa using diskF_faceInv h, diskF_faceStep⟩

/-- The complement of the face closure of the disk is invariant along face
orbits. -/
theorem diskFC_face_iff [Finite D] {x : D} : G.DiskFC r (G.face x) ↔ G.DiskFC r x :=
  ⟨fun h => by simpa using diskFC_faceInv h, diskFC_faceStep⟩

/-! ### The face band of the ring -/

/-- The face-closed disk lies in the disk. -/
theorem DiskF.diskN {x : D} (h : G.DiskF r x) : G.DiskN r x := h.1

/-- A dart of the face-closed disk lies off the ring. -/
theorem DiskF.not_mem {x : D} (h : G.DiskF r x) : x ∉ r := fun hx => h.2 (fband_of_mem hx)

/-- The face-closed disk lies in the interior of the disk. -/
theorem DiskF.diskE {x : D} (h : G.DiskF r x) : G.DiskE r x := ⟨h.1, h.not_mem⟩

/-- A dart of the disk that lies off the face band of the ring is in the
face-closed disk. -/
theorem diskF_of_diskN {x : D} (h : G.DiskN r x) (hb : ¬ G.Fband r x) : G.DiskF r x := ⟨h, hb⟩

/-- Off the face band of the ring, a dart lies in exactly one of the two
face-closed pieces. -/
theorem diskF_or_diskFC {x : D} (h : ¬ G.Fband r x) : G.DiskF r x ∨ G.DiskFC r x := by
  by_cases hN : G.DiskN r x
  · exact Or.inl ⟨hN, h⟩
  · exact Or.inr ⟨hN, h⟩

/-- The two face-closed pieces are disjoint. -/
theorem not_diskF_and_diskFC {x : D} : ¬ (G.DiskF r x ∧ G.DiskFC r x) :=
  fun h => h.2.1 h.1.1

/-- The kernel of the ring is the union of the two face-closed pieces. -/
theorem kernel_iff {x : D} : G.Kernel r x ↔ G.DiskF r x ∨ G.DiskFC r x := by
  refine ⟨diskF_or_diskFC, ?_⟩
  rintro (⟨-, hb⟩ | ⟨-, hb⟩) <;> exact hb

/-- The face band of the ring and the two face-closed pieces cover the darts. -/
theorem fband_or_diskF_or_diskFC (x : D) : G.Fband r x ∨ G.DiskF r x ∨ G.DiskFC r x := by
  by_cases hb : G.Fband r x
  · exact Or.inl hb
  · exact Or.inr (diskF_or_diskFC hb)

/-! ### Rotation invariance

The disk only depends on the extent of its ring, so it is unchanged by
rotation. -/

/-- Contour links out of the ring are unchanged by rotating it. -/
theorem dlink_rotate {n : ℕ} {x y : D} : G.DLink (r.rotate n) x y ↔ G.DLink r x y := by
  simp only [DLink, List.mem_rotate]

/-- Internally ring-disjoint contour paths are unchanged by rotating the
ring. -/
theorem dconnect_rotate {n : ℕ} {x y : D} :
    G.DConnect (r.rotate n) x y ↔ G.DConnect r x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (dlink_rotate.mp hbc)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (dlink_rotate.mpr hbc)

/-- The disk is unchanged by rotating its ring. -/
@[simp] theorem diskN_rotate {n : ℕ} {x : D} : G.DiskN (r.rotate n) x ↔ G.DiskN r x := by
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, List.mem_rotate.mp hy, dconnect_rotate.mp h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, List.mem_rotate.mpr hy, dconnect_rotate.mpr h⟩

/-- The interior of the disk is unchanged by rotating its ring. -/
@[simp] theorem diskE_rotate {n : ℕ} {x : D} : G.DiskE (r.rotate n) x ↔ G.DiskE r x := by
  simp only [DiskE, diskN_rotate, List.mem_rotate]

/-- The face-closed disk is unchanged by rotating its ring. -/
@[simp] theorem diskF_rotate {n : ℕ} {x : D} : G.DiskF (r.rotate n) x ↔ G.DiskF r x := by
  simp only [DiskF, diskN_rotate, fband_rotate]

/-- The complement of the face closure of the disk is unchanged by rotating its
ring. -/
@[simp] theorem diskFC_rotate {n : ℕ} {x : D} : G.DiskFC (r.rotate n) x ↔ G.DiskFC r x := by
  simp only [DiskFC, diskN_rotate, fband_rotate]


/-! ### Auxiliary chain lemmas

The contour arguments below stitch chains together at their endpoints, which
`List.getLastD` records without a nonemptiness proof. -/

section ListAux

variable {α : Type*} {R : α → α → Prop}

/-- The endpoint of a concatenation is the endpoint of its second part. -/
private theorem getLastD_append (x : α) (p q : List α) :
    (p ++ q).getLastD x = q.getLastD (p.getLastD x) := by
  match q with
  | [] => rw [List.append_nil]; rfl
  | a :: q => rw [getLastD_append_cons, getLastD_cons]

/-- Two chains meeting at the endpoint of the first one concatenate. -/
private theorem isChain_append_getLastD : ∀ {l₁ : List α} {x : α} {l₂ : List α},
    List.IsChain R (x :: l₁) → List.IsChain R (l₁.getLastD x :: l₂) →
      List.IsChain R (x :: (l₁ ++ l₂)) := by
  intro l₁
  induction l₁ with
  | nil => intro x l₂ _ h₂; exact h₂
  | cons a l₁ ih =>
    intro x l₂ h₁ h₂
    obtain ⟨hxa, htail⟩ := List.isChain_cons_cons.mp h₁
    rw [List.cons_append]
    exact List.IsChain.cons_cons hxa (ih htail (by rwa [getLastD_cons] at h₂))

/-- A reflexive-transitive chain of links is witnessed by a list. -/
private theorem exists_chain_of_reflTransGen {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ l : List α, List.IsChain R (a :: l) ∧ l.getLastD a = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], List.IsChain.singleton _, rfl⟩
  | head hab _ ih =>
    obtain ⟨l, hl, hlast⟩ := ih
    exact ⟨_ :: l, List.IsChain.cons_cons hab hl, by rw [getLastD_cons]; exact hlast⟩

end ListAux


/-! ### The ring contour

Cutting along the ring uses an auxiliary contour: the closed chain that follows
the faces of the ring links, crossing an edge at each ring dart.  This is the
`rclink` of the reference. -/

variable (G r)

open scoped Classical in
/-- The contour successor of a dart: darts on the ring step across their edge
first, darts off it step along their face. -/
noncomputable def RClink (x : D) : D := G.face (if x ∈ r then G.edge x else x)

variable {G r}

/-- On the ring the contour successor crosses the edge. -/
theorem rclink_of_mem {x : D} (hx : x ∈ r) : G.RClink r x = G.face (G.edge x) := by
  simp only [RClink, hx, ite_true]

/-- Off the ring the contour successor is the face successor. -/
theorem rclink_of_not_mem {x : D} (hx : x ∉ r) : G.RClink r x = G.face x := by
  simp only [RClink, hx, ite_false]

/-- The contour successor of a ring dart steps back along `node`. -/
theorem node_rclink_of_mem {x : D} (hx : x ∈ r) : G.node (G.RClink r x) = x := by
  rw [rclink_of_mem hx]; exact G.edgeK x

/-- Every dart is contour-linked to its contour successor. -/
theorem clink_rclink (x : D) : G.Clink x (G.RClink r x) := by
  by_cases hx : x ∈ r
  · exact Or.inl (node_rclink_of_mem hx).symm
  · rw [rclink_of_not_mem hx]; exact Or.inr rfl

/-- Stepping forward along `face` off the ring stays in the disk. -/
theorem diskN_face {x : D} (h : G.DiskN r x) (hx : x ∉ r) : G.DiskN r (G.face x) := by
  obtain ⟨y, hy, hpath⟩ := h
  exact ⟨y, hy, hpath.tail ⟨hx, Or.inr rfl⟩⟩

/-- Every face connection is realised by a duplicate-free face chain. -/
private theorem exists_nodup_faceChain [Finite D] {u v : D} (h : G.CFace u v) :
    ∃ c : List D, List.IsChain (fun a b => b = G.face a) (u :: c) ∧ (u :: c).Nodup ∧
      c.getLastD u = v := by
  obtain ⟨l, hl, hlast⟩ :=
    exists_chain_of_reflTransGen ((sameCycle_iff_reflTransGen G.face u v).mp h)
  obtain ⟨q, hq, hqn, hqlast, -⟩ := List.IsChain.exists_nodup hl
  exact ⟨q, hq, hqn, by rw [hqlast, hlast]⟩

/-- A duplicate-free face chain whose endpoint lies on a face-simple ring is a
contour chain: by simplicity none of its other darts lies on the ring. -/
private theorem isChain_rclink_of_faceChain [Finite D] (hsr : G.Simple r) :
    ∀ (u : D) (c : List D), List.IsChain (fun a b => b = G.face a) (u :: c) →
      (u :: c).Nodup → c.getLastD u ∈ r →
      List.IsChain (fun a b => b = G.RClink r a) (u :: c) := by
  intro u c
  induction c generalizing u with
  | nil => intro _ _ _; exact List.IsChain.singleton _
  | cons b c ih =>
    intro hc hu hlast
    rw [getLastD_cons] at hlast
    obtain ⟨hub, htail⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨hunotin, hnodup⟩ := List.nodup_cons.mp hu
    have hur : u ∉ r := by
      intro hur
      have hmem : c.getLastD b ∈ u :: b :: c :=
        List.mem_cons_of_mem _ (getLastD_mem_cons b c)
      have hface : G.CFace u (c.getLastD b) :=
        sameCycle_of_mem_isChain hc List.mem_cons_self hmem
      exact hunotin (hsr.eq_of_cface hur hlast hface ▸ getLastD_mem_cons b c)
    exact List.IsChain.cons_cons (hub.trans (rclink_of_not_mem hur).symm)
      (ih b htail hnodup hlast)

/-- The contour along a ring path: a duplicate-free contour chain out of `y`
that visits every dart of the path `p`, ends where `p` ends, and stays inside
the face band of `p`. -/
private theorem exists_ringContour [Finite D] (hsr : G.Simple r) :
    ∀ (p : List D) (y : D), y ∈ r → (∀ t ∈ p, t ∈ r) →
      List.IsChain G.Rlink (y :: p) → p.Nodup →
      ∃ c : List D, List.IsChain (fun a b => b = G.RClink r a) (y :: c) ∧ c.Nodup ∧
        c.getLastD y = p.getLastD y ∧ (∀ t ∈ p, t ∈ c) ∧ ∀ t, G.Fband c t → G.Fband p t := by
  intro p
  induction p with
  | nil =>
    intro y _ _ _ _
    exact ⟨[], List.IsChain.singleton _, List.nodup_nil, rfl, by simp, by simp⟩
  | cons z₀ p ih =>
    intro y hy hsub hchain hnodup
    obtain ⟨hyz₀, htail⟩ := List.isChain_cons_cons.mp hchain
    have hz₀r : z₀ ∈ r := hsub z₀ List.mem_cons_self
    have hsub' : ∀ t ∈ p, t ∈ r := fun t ht => hsub t (List.mem_cons_of_mem _ ht)
    obtain ⟨hz₀p, hnodup'⟩ := List.nodup_cons.mp hnodup
    obtain ⟨c₂, hc₂chain, hc₂nodup, hc₂last, hc₂sub, hc₂band⟩ :=
      ih z₀ hz₀r hsub' htail hnodup'
    have hwz₀ : G.CFace (G.face (G.edge y)) z₀ := (G.cface_face (G.edge y)).symm.trans hyz₀
    obtain ⟨c₁, hc₁chain, hc₁nodup, hc₁last⟩ := exists_nodup_faceChain hwz₀
    have hlast₁ : (G.face (G.edge y) :: c₁).getLastD y = z₀ := by
      rw [getLastD_cons, hc₁last]
    have hz₀mem : z₀ ∈ G.face (G.edge y) :: c₁ := hc₁last ▸ getLastD_mem_cons _ c₁
    have hface₁ : ∀ t ∈ G.face (G.edge y) :: c₁, G.CFace z₀ t := fun t ht =>
      sameCycle_of_mem_isChain hc₁chain hz₀mem ht
    refine ⟨(G.face (G.edge y) :: c₁) ++ c₂, ?_, ?_, ?_, ?_, ?_⟩
    · refine isChain_append_getLastD (List.IsChain.cons_cons ?_ ?_) ?_
      · rw [rclink_of_mem hy]
      · exact isChain_rclink_of_faceChain hsr _ _ hc₁chain hc₁nodup (hc₁last ▸ hz₀r)
      · rw [hlast₁]; exact hc₂chain
    · have hdisj : ∀ t ∈ G.face (G.edge y) :: c₁, t ∉ c₂ := by
        intro t ht ht₂
        obtain ⟨u, hu, htu⟩ := hc₂band t (fband_of_mem ht₂)
        exact hz₀p (hsr.eq_of_cface hz₀r (hsub' u hu) ((hface₁ t ht).trans htu) ▸ hu)
      refine List.nodup_append.mpr ⟨hc₁nodup, hc₂nodup, ?_⟩
      intro a ha b hb hab
      exact hdisj a ha (hab ▸ hb)
    · rw [getLastD_append, hlast₁, hc₂last, getLastD_cons]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact List.mem_append_left _ hz₀mem
      · exact List.mem_append_right _ (hc₂sub t ht)
    · intro t ht
      rcases fband_append.mp ht with ⟨u, hu, htu⟩ | ht
      · exact fband_cons.mpr (Or.inl (htu.trans (hface₁ u hu).symm))
      · exact fband_cons.mpr (Or.inr (hc₂band t ht))


/-! ### The interior of the disk is edge-closed

This is the only place where planarity is used.  If an edge left the interior,
the contour of the ring together with an escape path from the interior would
form a Moebius path, which a planar map does not have. -/

/-- A face chain that avoids the ring and starts in the disk ends in the
interior of the disk. -/
private theorem diskE_of_faceChain :
    ∀ (p : List D) (u : D), G.DiskN r u →
      List.IsChain (fun a b => b = G.face a) (u :: p) →
      (∀ t ∈ u :: p, t ∉ r) → G.DiskE r (p.getLastD u) := by
  intro p
  induction p with
  | nil => intro u hu _ hoff; exact ⟨hu, hoff u List.mem_cons_self⟩
  | cons a p ih =>
    intro u hu hchain hoff
    obtain ⟨hua, htail⟩ := List.isChain_cons_cons.mp hchain
    have hur : u ∉ r := hoff u List.mem_cons_self
    rw [getLastD_cons]
    exact ih a (by rw [hua]; exact diskN_face hu hur) htail
      (fun t ht => hoff t (List.mem_cons_of_mem _ ht))

/-- A list with a head splits at each of its darts into an initial segment
ending there and a remainder. -/
private theorem exists_split_getLastD {α : Type*} :
    ∀ (l : List α) (u v : α), v ∈ u :: l →
      ∃ d e : List α, u :: l = (u :: d) ++ e ∧ d.getLastD u = v := by
  intro l
  induction l with
  | nil =>
    intro u v hv
    rw [List.mem_singleton] at hv
    exact ⟨[], [], rfl, hv.symm⟩
  | cons a l ih =>
    intro u v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨[], a :: l, rfl, rfl⟩
    · obtain ⟨d, e, hde, hdlast⟩ := ih a v hv'
      exact ⟨a :: d, e, by rw [List.cons_append, ← hde], by rw [getLastD_cons, hdlast]⟩

/-- The last dart of a list with a head, as a `getLastD`. -/
private theorem getLast?_cons_eq {α : Type*} :
    ∀ (p : List α) (x : α), (x :: p).getLast? = some (p.getLastD x) := by
  intro p
  induction p with
  | nil => intro x; rfl
  | cons a p ih => intro x; rw [List.getLast?_cons_cons, ih a, getLastD_cons]

/-- The last dart of a list with a head, without its nonemptiness proof. -/
private theorem getLast_cons_eq_getLastD {α : Type*} (x : α) (p : List α) :
    (x :: p).getLast (List.cons_ne_nil x p) = p.getLastD x := by
  have h1 := List.getLast?_eq_some_getLast (List.cons_ne_nil x p)
  rw [getLast?_cons_eq] at h1
  exact (Option.some_inj.mp h1).symm

/-- The interior of the disk delimited by a ring is closed under `edge`. -/
theorem diskE_edge [Finite D] (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} (h : G.DiskE r x) : G.DiskE r (G.edge x) := by
  classical
  obtain ⟨hdN, hxr⟩ := h
  have hsr : G.Simple r := hscyc.simple
  obtain ⟨x', hx'def⟩ : ∃ w : D, w = G.face (G.edge x) := ⟨_, rfl⟩
  have hnx' : G.node x' = x := by rw [hx'def]; exact G.edgeK x
  have hdNx' : G.DiskN r x' := by
    have h1 : G.DiskN r (G.node⁻¹ x) := diskN_nodeInv hdN
    rwa [show G.node⁻¹ x = x' from by rw [Equiv.Perm.inv_eq_iff_eq, hnx']] at h1
  -- the face orbit of `x'`, which ends at `G.edge x`
  obtain ⟨a₀, q, hq₀⟩ := List.exists_cons_of_ne_nil (orbitList_ne_nil G.face x')
  have hq : orbitList G.face x' = x' :: q := by
    have hhd := head_orbitList G.face x'
    rw [hq₀] at hhd ⊢
    rw [List.headD_cons] at hhd
    rw [hhd]
  have hqchain : List.IsChain (fun a b => b = G.face a) (x' :: q) := by
    rw [← hq]; exact isChain_orbitList G.face x'
  have hqnodup : (x' :: q).Nodup := by rw [← hq]; exact nodup_orbitList G.face x'
  have hqmem : ∀ t : D, t ∈ x' :: q ↔ G.CFace x' t := by
    intro t; rw [← hq]; exact mem_orbitList
  have hqlast : q.getLastD x' = G.edge x := by
    have hcl := apply_getLastD_orbitList G.face x'
    rw [hq, getLastD_cons] at hcl
    exact G.face.injective (by rw [hcl, hx'def])
  by_cases hoffE : ∃ t ∈ x' :: q, t ∈ r
  case neg =>
    have hoff : ∀ t ∈ x' :: q, t ∉ r := fun t ht htr => hoffE ⟨t, ht, htr⟩
    rw [← hqlast]
    exact diskE_of_faceChain q x' hdNx' hqchain hoff
  -- the ring meets the face of `G.edge x`; rotate it to start there
  obtain ⟨y, hyq, hyr⟩ := hoffE
  obtain ⟨ra, rb, hrsplit⟩ := List.append_of_mem hyr
  obtain ⟨r₁, hr₁def⟩ : ∃ l : List D, l = rb ++ ra := ⟨_, rfl⟩
  have hrot : r.rotate ra.length = y :: r₁ := by
    rw [hrsplit, hr₁def,
      List.rotate_eq_drop_append_take (by simp), List.drop_left, List.take_left]
    rfl
  have hcycrr : IsCyclicChain G.Rlink (y :: r₁) := by
    rw [← hrot]; exact isCyclicChain_rotate.mpr hscyc.isCyclicChain
  have hsimrr : G.Simple (y :: r₁) := by
    rw [← hrot]; exact simple_rotate.mpr hsr
  have hmemrr : ∀ t : D, t ∈ y :: r₁ ↔ t ∈ r := by
    intro t; rw [← hrot]; exact List.mem_rotate
  obtain ⟨hr₁y, hr₁nodup⟩ := List.nodup_cons.mp hsimrr.nodup
  have hzy : G.Rlink (r₁.getLastD y) y := by
    have h1 := (isCyclicChain_cons.mp hcycrr).2
    rwa [getLast_cons_eq_getLastD] at h1
  have hzr : r₁.getLastD y ∈ r := (hmemrr _).mp (getLastD_mem_cons y r₁)
  obtain ⟨z', hz'def⟩ : ∃ w : D, w = G.face (G.edge (r₁.getLastD y)) := ⟨_, rfl⟩
  have hnz' : G.node z' = r₁.getLastD y := by rw [hz'def]; exact G.edgeK _
  have hyz' : G.CFace y z' := by
    rw [hz'def]; exact hzy.symm.trans (G.cface_face _)
  have hz'q : z' ∈ x' :: q := (hqmem z').mpr (((hqmem y).mp hyq).trans hyz')
  have hz'ne : z' ≠ x' := by
    intro heq
    have h1 : G.face (G.edge (r₁.getLastD y)) = G.face (G.edge x) := by
      rw [← hz'def, ← hx'def]; exact heq
    exact hxr (G.edge.injective (G.face.injective h1) ▸ hzr)
  have hz'mem : z' ∈ q := (List.mem_cons.mp hz'q).resolve_left hz'ne
  obtain ⟨q₁, q₂, hqsplit⟩ := List.append_of_mem hz'mem
  have hqcat : x' :: q = (x' :: q₁) ++ (z' :: q₂) := by rw [hqsplit]; rfl
  obtain ⟨hq₁chain, hq₂chain, hLq1'⟩ := List.isChain_append.mp (hqcat ▸ hqchain)
  have hLq1 : G.face (q₁.getLastD x') = z' :=
    (hLq1' _ (by rw [getLast?_cons_eq]; rfl) z' rfl).symm
  obtain ⟨hq₁nodup, hq₂nodup, hdisjq⟩ := List.nodup_append.mp (hqcat ▸ hqnodup)
  have hq₂last : q₂.getLastD z' = G.edge x := by
    rw [← hqlast, hqsplit, getLastD_append_cons]
  rcases List.mem_append.mp (hqcat ▸ hyq) with hy1 | hy2
  · -- the ring meets the first half: the second half is a face chain off the ring
    have hdNz' : G.DiskN r z' := by
      have h1 : G.DiskN r (G.node⁻¹ (r₁.getLastD y)) := diskN_nodeInv (diskN_of_mem hzr)
      rwa [show G.node⁻¹ (r₁.getLastD y) = z' from
        by rw [Equiv.Perm.inv_eq_iff_eq, hnz']] at h1
    have hoff2 : ∀ t ∈ z' :: q₂, t ∉ r := by
      intro t ht htr
      have hzt : G.CFace z' t :=
        sameCycle_of_mem_isChain hq₂chain List.mem_cons_self ht
      exact hdisjq y hy1 t ht (hsr.eq_of_cface hyr htr (hyz'.trans hzt))
    rw [← hq₂last]
    exact diskE_of_faceChain q₂ z' hdNz' hq₂chain hoff2
  -- the ring meets the second half: build the contour and contradict planarity
  obtain ⟨c₂, hc₂chain, hc₂nodup, hc₂last, hc₂sub, hc₂band⟩ :=
    exists_ringContour hsr r₁ y hyr (fun t ht => (hmemrr t).mp (List.mem_cons_of_mem _ ht))
      hcycrr.isChain hr₁nodup
  have hc₂ny : ∀ t ∈ c₂, ¬ G.CFace y t := by
    intro t ht hyt
    obtain ⟨u, hu, htu⟩ := hc₂band t (fband_of_mem ht)
    exact hr₁y (hsr.eq_of_cface hyr ((hmemrr u).mp (List.mem_cons_of_mem _ hu))
      (hyt.trans htu) ▸ hu)
  obtain ⟨d, e, hde, hdlast⟩ := exists_split_getLastD q₂ z' y hy2
  have hdsub : ∀ t ∈ z' :: d, t ∈ z' :: q₂ := by
    intro t ht; rw [hde]; exact List.mem_append_left _ ht
  have hdchain : List.IsChain (fun a b => b = G.face a) (z' :: d) :=
    (List.isChain_append.mp (hde ▸ hq₂chain)).1
  have hdnodup : (z' :: d).Nodup := (List.nodup_append.mp (hde ▸ hq₂nodup)).1
  -- the contour `z' :: c`
  obtain ⟨c, hcdef⟩ : ∃ l : List D, l = d ++ c₂ := ⟨_, rfl⟩
  have hcface : ∀ t ∈ z' :: d, G.CFace y t := by
    intro t ht
    exact sameCycle_of_mem_isChain hdchain (hdlast ▸ getLastD_mem_cons z' d) ht
  have hcchain : List.IsChain (fun a b => b = G.RClink r a) (z' :: c) := by
    rw [hcdef]
    refine isChain_append_getLastD
      (isChain_rclink_of_faceChain hsr z' d hdchain hdnodup (hdlast ▸ hyr)) ?_
    rw [hdlast]; exact hc₂chain
  have hcnodup : (z' :: c).Nodup := by
    rw [hcdef, ← List.cons_append]
    refine List.nodup_append.mpr ⟨hdnodup, hc₂nodup, ?_⟩
    intro a ha b hb hab
    exact hc₂ny b (hab ▸ hb) (hab ▸ hcface a ha)
  have hclast : c.getLastD z' = r₁.getLastD y := by
    rw [hcdef, getLastD_append, hdlast, hc₂last]
  have hcsub : ∀ t ∈ y :: r₁, t ∈ z' :: c := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hcdef, ← hdlast]
      exact List.mem_append_left _ (getLastD_mem_cons z' d)
    · rw [hcdef]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (hc₂sub t ht))
  have hcq₁ : ∀ t ∈ z' :: c, t ∉ x' :: q₁ := by
    intro t ht ht₁
    rw [hcdef] at ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hdisjq t ht₁ t List.mem_cons_self rfl
    rcases List.mem_append.mp ht with ht | ht
    · exact hdisjq t ht₁ t (hdsub t (List.mem_cons_of_mem _ ht)) rfl
    · refine hc₂ny t ht (hyz'.trans ?_)
      have h1 : G.CFace (q₁.getLastD x') t :=
        sameCycle_of_mem_isChain hq₁chain (getLastD_mem_cons x' q₁) ht₁
      exact ((hLq1 ▸ G.cface_face (q₁.getLastD x')).symm).trans h1
  have hcyclic : IsCyclicChain (fun a b => b = G.RClink r a) (z' :: c) := by
    refine isCyclicChain_cons.mpr ⟨hcchain, ?_⟩
    show z' = G.RClink r ((z' :: c).getLast (List.cons_ne_nil z' c))
    rw [getLast_cons_eq_getLastD, hclast, rclink_of_mem hzr, hz'def]
  have hLclosed : ∀ u ∈ z' :: c, G.RClink r u ∈ z' :: c := fun u hu =>
    mem_of_isCyclicChain hcyclic hu
  have hx'L : x' ∉ z' :: c := fun hc => hcq₁ x' hc List.mem_cons_self
  -- an escape path from the disk to the contour
  obtain ⟨x₀, hx₀r, hx₀path⟩ := hdN
  obtain ⟨pp, hppchain, hpplast⟩ := exists_chain_of_reflTransGen hx₀path
  have hx₀L : G.node⁻¹ x₀ ∈ z' :: c := by
    have h1 : G.RClink r x₀ ∈ z' :: c :=
      hLclosed x₀ (hcsub x₀ ((hmemrr x₀).mpr hx₀r))
    rwa [show G.RClink r x₀ = G.node⁻¹ x₀ from
      by rw [Equiv.Perm.eq_inv_iff_eq, node_rclink_of_mem hx₀r]] at h1
  have key : ∀ (pl : List D) (u : D), List.IsChain (G.DLink r) (u :: pl) →
      pl.getLastD u = x → (∃ t ∈ u :: pl, t ∈ z' :: c) →
      ∃ (x₁ : D) (ql : List D), G.node x₁ ∈ z' :: c ∧ List.IsChain G.Clink (x₁ :: ql) ∧
        ql.getLastD x₁ = x' ∧ ∀ t ∈ x₁ :: ql, t ∉ z' :: c := by
    intro pl
    induction pl with
    | nil =>
      intro u _ hlast hmem
      obtain ⟨t, ht, htL⟩ := hmem
      rw [List.mem_singleton] at ht
      subst ht
      refine ⟨x', [], ?_, List.IsChain.singleton _, rfl, ?_⟩
      · rw [hnx', ← hlast]; exact htL
      · intro s hs; rw [List.mem_singleton] at hs; subst hs; exact hx'L
    | cons a pl ih =>
      intro u hchain hlast hmem
      obtain ⟨hua, htail⟩ := List.isChain_cons_cons.mp hchain
      rw [getLastD_cons] at hlast
      by_cases hpE : ∃ t ∈ a :: pl, t ∈ z' :: c
      · exact ih a htail hlast hpE
      have hp : ∀ t ∈ a :: pl, t ∉ z' :: c := fun t ht htL => hpE ⟨t, ht, htL⟩
      obtain ⟨hur, hclink⟩ := hua
      have huL : u ∈ z' :: c := by
        obtain ⟨t, ht, htL⟩ := hmem
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact htL
        · exact absurd htL (hp t ht')
      have hfaceL : G.face u ∈ z' :: c := by
        have h1 := hLclosed u huL
        rwa [rclink_of_not_mem hur] at h1
      have hna : G.node a = u := by
        rcases hclink with h1 | h2
        · exact h1.symm
        · exact absurd (h2 ▸ hfaceL) (hp a List.mem_cons_self)
      refine ⟨a, pl ++ [x'], by rw [hna]; exact huL, ?_, ?_, ?_⟩
      · refine isChain_append_getLastD (List.IsChain.imp (fun _ _ hd => hd.2) htail) ?_
        rw [hlast]
        exact List.IsChain.cons_cons (Or.inl hnx'.symm) (List.IsChain.singleton _)
      · rw [getLastD_append]; rfl
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hp _ List.mem_cons_self
        rcases List.mem_append.mp ht' with h1 | h1
        · exact hp _ (List.mem_cons_of_mem _ h1)
        · rw [List.mem_singleton] at h1; subst h1; exact hx'L
  obtain ⟨x₁, pth, hnx₁L, hpthchain, hpthlast, hpthoff⟩ :=
    key pp (G.node⁻¹ x₀) hppchain hpplast ⟨G.node⁻¹ x₀, List.mem_cons_self, hx₀L⟩
  -- extend the escape path along the first half of the face cycle
  have hq₁clink : List.IsChain G.Clink (x' :: q₁) :=
    List.IsChain.imp (fun _ _ hf => Or.inr hf.symm) hq₁chain
  have hc0chain : List.IsChain G.Clink (x₁ :: (pth ++ q₁)) :=
    isChain_append_getLastD hpthchain (by rw [hpthlast]; exact hq₁clink)
  have hc0last : (pth ++ q₁).getLastD x₁ = q₁.getLastD x' := by
    rw [getLastD_append, hpthlast]
  have hc0off : ∀ t ∈ x₁ :: (pth ++ q₁), t ∉ z' :: c := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact hpthoff _ List.mem_cons_self
    rcases List.mem_append.mp ht' with h1 | h1
    · exact hpthoff _ (List.mem_cons_of_mem _ h1)
    · exact fun hL => hcq₁ _ hL (List.mem_cons_of_mem _ h1)
  obtain ⟨c₁, hc₁chain, hc₁nodup, hc₁last, hc₁sub⟩ := List.IsChain.exists_nodup hc0chain
  -- the Moebius path
  have hcclink : List.IsChain G.Clink (z' :: c) :=
    List.IsChain.imp (fun a _ hf => by rw [hf]; exact clink_rclink a) hcchain
  have hdata : G.MoebiusData x₁ (c₁ ++ z' :: c) z' := by
    refine ⟨?_, ?_, ?_, c₁, c, rfl, List.mem_cons.mp hnx₁L⟩
    · refine List.nodup_append.mpr ⟨hc₁nodup, hcnodup, ?_⟩
      intro s hs t ht hst
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hc0off _ List.mem_cons_self (hst ▸ ht)
      · exact hc0off _ (List.mem_cons_of_mem _ (hc₁sub _ hs')) (hst ▸ ht)
    · refine isChain_append_cons hc₁chain ?_ hcclink
      rw [hc₁last, hc0last]
      exact Or.inr hLq1
    · rw [getLastD_append_cons, hclast, hnz']
  have hjordan : G.Jordan := hplan.jordan
  exact absurd (G.moebiusPath_of_data hdata) (hjordan _)

/-- The interior of the disk is closed under `edge` backwards. -/
theorem diskE_edgeInv [Finite D] (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} (h : G.DiskE r x) : G.DiskE r (G.edge⁻¹ x) := by
  refine closed_of_closed_inv (f := G.edge⁻¹) (fun z hz => ?_) h
  rw [inv_inv]
  exact diskE_edge hplan hscyc hz

/-- The interior of the disk is invariant along edge orbits. -/
theorem diskE_edge_iff [Finite D] (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} : G.DiskE r (G.edge x) ↔ G.DiskE r x := by
  refine ⟨fun h => ?_, diskE_edge hplan hscyc⟩
  simpa using diskE_edgeInv hplan hscyc h

/-- The disk is closed under `edge` away from its ring. -/
theorem diskN_edge_of_not_mem [Finite D] (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} (h : G.DiskN r x) (hx : x ∉ r) : G.DiskN r (G.edge x) :=
  (diskE_edge hplan hscyc ⟨h, hx⟩).1

/-- An edge out of the face-closed disk lands in the interior of the disk. -/
theorem diskE_edge_of_diskF [Finite D] (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} (h : G.DiskF r x) : G.DiskE r (G.edge x) :=
  diskE_edge hplan hscyc h.diskE

/-! ### Cyclic chains and cyclic successors

The two border rings of the snip construction are cycles for the cyclic
successor of a list, so the cyclic chain condition has to be read off the
`List.next` function. -/

section ListCyclic

variable {α : Type*}

/-- In a cyclic chain, cyclically consecutive positions are linked. -/
private theorem rel_getElem_succ {e : α → α → Prop} {l : List α} (hcyc : IsCyclicChain e l)
    {i k : ℕ} (hi : i < l.length) (hk : k < l.length) (hik : k = (i + 1) % l.length) :
    e l[i] l[k] := by
  rcases Nat.lt_or_ge (i + 1) l.length with hlt | hge
  · have hk' : k = i + 1 := by rw [hik, Nat.mod_eq_of_lt hlt]
    subst hk'
    exact List.isChain_iff_getElem.mp hcyc.isChain i hlt
  · have hi1 : i + 1 = l.length := by omega
    have hi' : l.length - 1 = i := by omega
    have hk0 : k = 0 := by rw [hik, hi1, Nat.mod_self]
    subst hk0
    have hmem1 : l[i] ∈ l.getLast? := by
      rw [Option.mem_def, List.getLast?_eq_getElem?, hi', List.getElem?_eq_getElem hi]
    have hmem2 : l[0] ∈ l.head? := by
      rw [Option.mem_def, List.head?_eq_getElem?, List.getElem?_eq_getElem]
    exact hcyc.2 _ hmem1 _ hmem2

/-- In a duplicate-free cyclic chain each dart is linked to its cyclic
successor. -/
private theorem rel_next [DecidableEq α] {e : α → α → Prop} {l : List α}
    (hcyc : IsCyclicChain e l) (hl : l.Nodup) {x : α} (hx : x ∈ l) : e x (l.next x hx) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem l hl i hi]
  exact rel_getElem_succ hcyc hi _ rfl

/-- A list is a cyclic chain for a function exactly when mapping that function
rotates it by one step. -/
private theorem isCyclicChain_of_map_eq_rotate {F : α → α} {l : List α}
    (h : l.map F = l.rotate 1) : IsCyclicChain (fun a b => b = F a) l := by
  have hget : ∀ (i k : ℕ) (hi : i < l.length) (hk : k < l.length),
      k = (i + 1) % l.length → F l[i] = l[k] := by
    intro i k hi hk hik
    have h2 := List.getElem_of_eq h (show i < (l.map F).length by simpa using hi)
    rw [List.getElem_map, List.getElem_rotate] at h2
    subst hik
    exact h2
  refine ⟨List.isChain_iff_getElem.mpr ?_, ?_⟩
  · intro i hi
    exact (hget i (i + 1) (by omega) hi (by rw [Nat.mod_eq_of_lt hi])).symm
  · intro a ha b hb
    have hne : l ≠ [] := by
      intro h0; rw [h0] at ha; simp at ha
    have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    have hae : a = l[l.length - 1] := by
      rw [Option.mem_def, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)] at ha
      exact (Option.some_inj.mp ha).symm
    have hbe : b = l[0] := by
      rw [Option.mem_def, List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at hb
      exact (Option.some_inj.mp hb).symm
    rw [hae, hbe]
    exact (hget (l.length - 1) 0 (by omega) hpos
      (by rw [Nat.sub_add_cancel hpos, Nat.mod_self])).symm

/-- The cyclic successor only depends on the dart. -/
private theorem next_congr [DecidableEq α] {l : List α} {a b : α} (hab : a = b)
    (ha : a ∈ l) (hb : b ∈ l) : l.next a ha = l.next b hb := by
  subst hab; rfl

end ListCyclic

/-! ### The disk map

Cutting `G` along the ring yields two hypermaps.  On the disk side the darts
are those of `DiskN r`, and the ring becomes an E-cycle: the `edge` map follows
the ring there, while the `face` map crosses back over the edge of the
preceding ring dart. -/

section SnipDisk

variable [DecidableEq D]

variable (G r)

/-- The `edge` map of the disk map: along the ring it is the ring's own cyclic
successor, and elsewhere it is the `edge` of `G`. -/
def snipdEdge (x : D) : D := if h : x ∈ r then r.next x h else G.edge x

/-- The `face` map of the disk map: along the ring it crosses the edge of the
preceding ring dart, and elsewhere it is the `face` of `G`. -/
def snipdFace (x : D) : D := if h : x ∈ r then G.face (G.edge (r.prev x h)) else G.face x

variable {G r}

/-- On the ring the disk's `edge` map is the ring's cyclic successor. -/
theorem snipdEdge_of_mem {x : D} (hx : x ∈ r) : G.snipdEdge r x = r.next x hx := dite_eq_left hx

/-- Off the ring the disk's `edge` map is the `edge` of `G`. -/
theorem snipdEdge_of_not_mem {x : D} (hx : x ∉ r) : G.snipdEdge r x = G.edge x := dite_eq_right hx

/-- On the ring the disk's `face` map crosses the preceding ring edge. -/
theorem snipdFace_of_mem {x : D} (hx : x ∈ r) :
    G.snipdFace r x = G.face (G.edge (r.prev x hx)) := dite_eq_left hx

/-- Off the ring the disk's `face` map is the `face` of `G`. -/
theorem snipdFace_of_not_mem {x : D} (hx : x ∉ r) : G.snipdFace r x = G.face x := dite_eq_right hx

variable [Finite D]

/-- The disk's `edge` map stays inside the disk. -/
theorem diskN_snipdEdge (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {x : D} (h : G.DiskN r x) : G.DiskN r (G.snipdEdge r x) := by
  by_cases hx : x ∈ r
  · rw [snipdEdge_of_mem hx]
    exact diskN_of_mem (List.next_mem _ _ _)
  · rw [snipdEdge_of_not_mem hx]
    exact diskN_edge_of_not_mem hplan hscyc h hx

/-- The disk's `face` map stays inside the disk. -/
theorem diskN_snipdFace {x : D} (h : G.DiskN r x) : G.DiskN r (G.snipdFace r x) := by
  by_cases hx : x ∈ r
  · rw [snipdFace_of_mem hx]
    refine diskN_node_iff.mp ?_
    rw [G.edgeK]
    exact diskN_of_mem (List.prev_mem _ _ _)
  · rw [snipdFace_of_not_mem hx]
    exact diskN_face h hx

/-- The triangular identity of the disk map. -/
theorem snipd_cancel3 (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) {x : D} (hx : G.DiskN r x) :
    G.node (G.snipdFace r (G.snipdEdge r x)) = x := by
  by_cases hxr : x ∈ r
  · rw [snipdEdge_of_mem hxr, snipdFace_of_mem (List.next_mem _ _ _),
      List.prev_next r hscyc.nodup x hxr, G.edgeK]
  · have hedge : G.edge x ∉ r := (diskE_edge hplan hscyc ⟨hx, hxr⟩).2
    rw [snipdEdge_of_not_mem hxr, snipdFace_of_not_mem hedge, G.edgeK]

variable (G r)

/-- The disk map: the hypermap carried by the darts of the disk. -/
noncomputable def snipDisk (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    Hypermap {x : D // G.DiskN r x} :=
  Hypermap.ofCancel3
    (fun u => ⟨G.snipdEdge r u.1, diskN_snipdEdge hplan hscyc u.2⟩)
    (fun u => ⟨G.node u.1, diskN_node u.2⟩)
    (fun u => ⟨G.snipdFace r u.1, diskN_snipdFace u.2⟩)
    (fun u => Subtype.ext (snipd_cancel3 hplan hscyc u.2))

variable {G r}

/-- The `edge` map of the disk map, read in `G`. -/
@[simp] theorem snipDisk_edge (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // G.DiskN r x}) : ((snipDisk G r hplan hscyc).edge u).1 = G.snipdEdge r u.1 :=
  rfl

/-- The `node` map of the disk map, read in `G`. -/
@[simp] theorem snipDisk_node (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // G.DiskN r x}) : ((snipDisk G r hplan hscyc).node u).1 = G.node u.1 := rfl

/-- The `face` map of the disk map, read in `G`. -/
@[simp] theorem snipDisk_face (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // G.DiskN r x}) : ((snipDisk G r hplan hscyc).face u).1 = G.snipdFace r u.1 :=
  rfl

variable (G r)

/-- The projection of a disk dart back into `G`. -/
def snipd (u : {x : D // G.DiskN r x}) : D := u.1

/-- The border of the disk map: the ring lifted into the disk. -/
def snipdRing : List {x : D // G.DiskN r x} :=
  r.pmap (fun x (h : x ∈ r) => (⟨x, diskN_of_mem h⟩ : {x : D // G.DiskN r x})) fun _ h => h

variable {G r}

omit [DecidableEq D] [Finite D] in
/-- The disk projection is injective. -/
theorem snipd_injective : Function.Injective (G.snipd r) := fun _ _ h => Subtype.ext h

omit [DecidableEq D] in
/-- The border of the disk map projects onto the ring. -/
@[simp] theorem map_snipdRing : (G.snipdRing r).map (G.snipd r) = r := by
  rw [snipdRing, List.map_pmap]
  simp [snipd]

omit [DecidableEq D] in
/-- A disk dart lies on the border exactly when it lies on the ring. -/
theorem mem_snipdRing {u : {x : D // G.DiskN r x}} : u ∈ G.snipdRing r ↔ G.snipd r u ∈ r := by
  constructor
  · intro h
    have h2 : G.snipd r u ∈ (G.snipdRing r).map (G.snipd r) := List.mem_map_of_mem h
    rwa [map_snipdRing] at h2
  · intro h
    have h2 : G.snipd r u ∈ (G.snipdRing r).map (G.snipd r) := by
      rw [map_snipdRing]; exact h
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp h2
    rwa [snipd_injective hveq] at hv

omit [DecidableEq D] in
/-- The border of the disk map has no repetitions. -/
theorem nodup_snipdRing (hscyc : G.Scycle G.Rlink r) : (G.snipdRing r).Nodup :=
  List.Nodup.of_map _ (by rw [map_snipdRing]; exact hscyc.nodup)

/-- The border of the disk map is an E-cycle. -/
theorem isCyclicChain_snipdRing (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    IsCyclicChain (fun u v => v = (snipDisk G r hplan hscyc).edge u) (G.snipdRing r) := by
  refine isCyclicChain_of_map_eq_rotate ?_
  refine List.map_injective_iff.mpr (snipd_injective (G := G) (r := r)) ?_
  rw [List.map_map, List.map_rotate, map_snipdRing, snipdRing, List.map_pmap,
    ← List.pmap_next_eq_rotate_one r hscyc.nodup]
  refine List.pmap_congr_left _ ?_
  intro a ha _ _
  exact snipdEdge_of_mem ha

/-- The disk projection carries face orbits of the disk map into face orbits
of `G`. -/
theorem cface_snipd (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {u v : {x : D // G.DiskN r x}} (h : (snipDisk G r hplan hscyc).CFace u v) :
    G.CFace (G.snipd r u) (G.snipd r v) := by
  have hstep : ∀ w : {x : D // G.DiskN r x},
      G.CFace (G.snipd r w) (G.snipd r ((snipDisk G r hplan hscyc).face w)) := by
    intro w
    change G.CFace w.1 (G.snipdFace r w.1)
    by_cases hw : w.1 ∈ r
    · rw [snipdFace_of_mem hw]
      have h1 := rel_next hscyc.isCyclicChain hscyc.nodup (List.prev_mem r w.1 hw)
      rw [List.next_prev r hscyc.nodup w.1 hw] at h1
      exact h1.symm.trans (G.cface_face _)
    · rw [snipdFace_of_not_mem hw]
      exact G.cface_face w.1
  replace h := (sameCycle_iff_reflTransGen (snipDisk G r hplan hscyc).face u v).mp h
  induction h with
  | refl => exact SameCycle.refl _ _
  | tail _ hbc ih =>
    rw [hbc]
    exact ih.trans (hstep _)

/-- The border of the disk map is face-simple. -/
theorem simple_snipdRing (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    (snipDisk G r hplan hscyc).Simple (G.snipdRing r) := by
  refine List.Pairwise.imp_of_mem ?_ (nodup_snipdRing hscyc)
  intro a b ha hb hab hcf
  exact hab (snipd_injective (hscyc.simple.eq_of_cface (mem_snipdRing.mp ha)
    (mem_snipdRing.mp hb) (cface_snipd hplan hscyc hcf)))

/-- The border of the disk map is a face-simple E-cycle. -/
theorem scycle_snipdRing (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    (snipDisk G r hplan hscyc).Scycle
      (fun u v => v = (snipDisk G r hplan hscyc).edge u) (G.snipdRing r) :=
  ⟨isCyclicChain_snipdRing hplan hscyc, simple_snipdRing hplan hscyc⟩

end SnipDisk

/-! ### The remainder map

On the remainder side the darts are those *outside* the interior of the disk,
so the ring becomes an N-cycle: the `node` map follows the ring backwards
there, while the `face` map jumps onto the ring whenever it would enter the
disk. -/

section SnipRem

variable [DecidableEq D] [Finite D]

variable (G r)

/-- The `node` map of the remainder map: along the ring it is the ring's cyclic
predecessor, and elsewhere it is the `node` of `G`. -/
def sniprNode (x : D) : D := if h : x ∈ r then r.prev x h else G.node x

/-- The `face` map of the remainder map: it steps onto the ring whenever the
`face` step of `G` would enter the disk. -/
def sniprFace (x : D) : D :=
  if h : G.node (G.face x) ∈ r then r.next (G.node (G.face x)) h else G.face x

variable {G r}

omit [Finite D] in
/-- On the ring the remainder's `node` map is the ring's cyclic predecessor. -/
theorem sniprNode_of_mem {x : D} (hx : x ∈ r) : G.sniprNode r x = r.prev x hx :=
  dite_eq_left hx

omit [Finite D] in
/-- Off the ring the remainder's `node` map is the `node` of `G`. -/
theorem sniprNode_of_not_mem {x : D} (hx : x ∉ r) : G.sniprNode r x = G.node x :=
  dite_eq_right hx

omit [Finite D] in
/-- Where the `face` step of `G` would enter the disk, the remainder's `face`
map steps along the ring instead. -/
theorem sniprFace_of_mem {x : D} (hx : G.node (G.face x) ∈ r) :
    G.sniprFace r x = r.next (G.node (G.face x)) hx := dite_eq_left hx

omit [Finite D] in
/-- Elsewhere the remainder's `face` map is the `face` of `G`. -/
theorem sniprFace_of_not_mem {x : D} (hx : G.node (G.face x) ∉ r) :
    G.sniprFace r x = G.face x := dite_eq_right hx

omit [DecidableEq D] in
/-- The complement of the interior of the disk is closed under `edge`. -/
theorem not_diskE_edge (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) {x : D}
    (h : ¬ G.DiskE r x) : ¬ G.DiskE r (G.edge x) :=
  fun hc => h ((diskE_edge_iff hplan hscyc).mp hc)

/-- The remainder's `node` map stays outside the interior of the disk. -/
theorem not_diskE_sniprNode {x : D} (h : ¬ G.DiskE r x) :
    ¬ G.DiskE r (G.sniprNode r x) := by
  by_cases hx : x ∈ r
  · rw [sniprNode_of_mem hx]
    exact fun hc => hc.2 (List.prev_mem _ _ _)
  · rw [sniprNode_of_not_mem hx]
    exact fun hc => h ⟨diskN_node_iff.mp hc.1, hx⟩

/-- The remainder's `face` map stays outside the interior of the disk. -/
theorem not_diskE_sniprFace (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) {x : D}
    (h : ¬ G.DiskE r x) : ¬ G.DiskE r (G.sniprFace r x) := by
  by_cases hx : G.node (G.face x) ∈ r
  · rw [sniprFace_of_mem hx]
    exact fun hc => hc.2 (List.next_mem _ _ _)
  · rw [sniprFace_of_not_mem hx]
    intro hc
    refine h ?_
    have h2 := diskE_edge hplan hscyc (⟨diskN_node hc.1, hx⟩ : G.DiskE r (G.node (G.face x)))
    rwa [G.faceK] at h2

/-- The triangular identity of the remainder map. -/
theorem snipr_cancel3 (hscyc : G.Scycle G.Rlink r) {x : D}
    (hx : ¬ G.DiskE r x) : G.sniprNode r (G.sniprFace r (G.edge x)) = x := by
  by_cases hxr : x ∈ r
  · have hn : G.node (G.face (G.edge x)) ∈ r := by rw [G.edgeK]; exact hxr
    rw [sniprFace_of_mem hn, next_congr (G.edgeK x) hn hxr,
      sniprNode_of_mem (List.next_mem _ _ _), List.prev_next r hscyc.nodup x hxr]
  · have hn : G.node (G.face (G.edge x)) ∉ r := by rw [G.edgeK]; exact hxr
    have hfe : G.face (G.edge x) ∉ r := by
      intro hc
      refine hx ⟨?_, hxr⟩
      have h2 : G.DiskN r (G.node (G.face (G.edge x))) := diskN_node (diskN_of_mem hc)
      rwa [G.edgeK] at h2
    rw [sniprFace_of_not_mem hn, sniprNode_of_not_mem hfe, G.edgeK]

variable (G r)

/-- The remainder map: the hypermap carried by the darts outside the interior
of the disk. -/
noncomputable def snipRem (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    Hypermap {x : D // ¬ G.DiskE r x} :=
  Hypermap.ofCancel3
    (fun u => ⟨G.edge u.1, not_diskE_edge hplan hscyc u.2⟩)
    (fun u => ⟨G.sniprNode r u.1, not_diskE_sniprNode u.2⟩)
    (fun u => ⟨G.sniprFace r u.1, not_diskE_sniprFace hplan hscyc u.2⟩)
    (fun u => Subtype.ext (snipr_cancel3 hscyc u.2))

/-- The projection of a remainder dart back into `G`. -/
def snipr (u : {x : D // ¬ G.DiskE r x}) : D := u.1

/-- The border of the remainder map: the ring, traversed backwards. -/
def sniprRing : List {x : D // ¬ G.DiskE r x} :=
  r.reverse.pmap (fun x (h : x ∈ r.reverse) =>
    (⟨x, fun hc => hc.2 (List.mem_reverse.mp h)⟩ : {x : D // ¬ G.DiskE r x})) fun _ h => h

variable {G r}

/-- The `edge` map of the remainder map, read in `G`. -/
@[simp] theorem snipRem_edge (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // ¬ G.DiskE r x}) : ((snipRem G r hplan hscyc).edge u).1 = G.edge u.1 := rfl

/-- The `node` map of the remainder map, read in `G`. -/
@[simp] theorem snipRem_node (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // ¬ G.DiskE r x}) :
    ((snipRem G r hplan hscyc).node u).1 = G.sniprNode r u.1 := rfl

/-- The `face` map of the remainder map, read in `G`. -/
@[simp] theorem snipRem_face (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    (u : {x : D // ¬ G.DiskE r x}) :
    ((snipRem G r hplan hscyc).face u).1 = G.sniprFace r u.1 := rfl

omit [DecidableEq D] [Finite D] in
/-- The remainder projection is injective. -/
theorem snipr_injective : Function.Injective (G.snipr r) := fun _ _ h => Subtype.ext h

omit [DecidableEq D] [Finite D] in
/-- The border of the remainder map projects onto the reversed ring. -/
@[simp] theorem map_sniprRing : (G.sniprRing r).map (G.snipr r) = r.reverse := by
  rw [sniprRing, List.map_pmap]
  simp [snipr]

omit [DecidableEq D] [Finite D] in
/-- A remainder dart lies on the border exactly when it lies on the ring. -/
theorem mem_sniprRing {u : {x : D // ¬ G.DiskE r x}} :
    u ∈ G.sniprRing r ↔ G.snipr r u ∈ r := by
  constructor
  · intro h
    have h2 : G.snipr r u ∈ (G.sniprRing r).map (G.snipr r) := List.mem_map_of_mem h
    rw [map_sniprRing] at h2
    exact List.mem_reverse.mp h2
  · intro h
    have h2 : G.snipr r u ∈ (G.sniprRing r).map (G.snipr r) := by
      rw [map_sniprRing]; exact List.mem_reverse.mpr h
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp h2
    rwa [snipr_injective hveq] at hv

omit [DecidableEq D] [Finite D] in
/-- The border of the remainder map has no repetitions. -/
theorem nodup_sniprRing (hscyc : G.Scycle G.Rlink r) : (G.sniprRing r).Nodup :=
  List.Nodup.of_map _ (by rw [map_sniprRing]; exact List.nodup_reverse.mpr hscyc.nodup)

/-- The border of the remainder map is an N-cycle. -/
theorem isCyclicChain_sniprRing (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    IsCyclicChain (fun u v => v = (snipRem G r hplan hscyc).node u) (G.sniprRing r) := by
  refine isCyclicChain_of_map_eq_rotate ?_
  refine List.map_injective_iff.mpr (snipr_injective (G := G) (r := r)) ?_
  rw [List.map_map, List.map_rotate, map_sniprRing, sniprRing, List.map_pmap,
    ← List.pmap_next_eq_rotate_one r.reverse (List.nodup_reverse.mpr hscyc.nodup)]
  refine List.pmap_congr_left _ ?_
  intro a ha _ _
  change G.sniprNode r a = _
  rw [sniprNode_of_mem (List.mem_reverse.mp ha)]
  exact (List.next_reverse_eq_prev r hscyc.nodup a (List.mem_reverse.mp ha)).symm

end SnipRem

/-! ### The snip construction is a patch

The disk map and the remainder map glue back to `G` along their two border
rings: this is the reference's `snip_patch`. -/

section SnipPatch

variable [DecidableEq D] [Finite D]

/-- **Cutting a planar map along a simple ring** exhibits it as the patch of
the disk map and the remainder map along their border rings. -/
theorem snip_patch (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    Patch G (snipDisk G r hplan hscyc) (snipRem G r hplan hscyc)
      (G.snipd r) (G.snipr r) (G.snipdRing r) (G.sniprRing r) where
  injd := snipd_injective
  injr := snipr_injective
  scycle_d := scycle_snipdRing hplan hscyc
  cycle_r := isCyclicChain_sniprRing hplan hscyc
  nodup_r := nodup_sniprRing hscyc
  ring := by rw [map_sniprRing, map_snipdRing]
  range_r := by
    intro x
    have h1 : x ∈ Set.range (G.snipr r) ↔ ¬ G.DiskE r x :=
      ⟨by rintro ⟨u, rfl⟩; exact u.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
    have h2 : x ∈ Set.range (G.snipd r) ↔ G.DiskN r x :=
      ⟨by rintro ⟨u, rfl⟩; exact u.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
    rw [h1, h2, map_snipdRing, DiskE]
    tauto
  edge_d := by
    intro xd hxd
    exact snipdEdge_of_not_mem fun hc => hxd (mem_snipdRing.mpr hc)
  node_d := fun _ => rfl
  edge_r := fun _ => rfl
  node_r := by
    intro xr hxr
    exact sniprNode_of_not_mem fun hc => hxr (mem_sniprRing.mpr hc)

/-- The disk map of a planar map is planar. -/
theorem planar_snipDisk (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    (snipDisk G r hplan hscyc).Planar :=
  ((snip_patch hplan hscyc).planar_patch.mp hplan).1

/-- The remainder map of a planar map is planar. -/
theorem planar_snipRem (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    (snipRem G r hplan hscyc).Planar :=
  ((snip_patch hplan hscyc).planar_patch.mp hplan).2

end SnipPatch

end Hypermap

end FourColor

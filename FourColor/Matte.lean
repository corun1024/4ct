import FourColor.Grid

/-!
# Mattes

A *matte* is a finite set of grid pixels delimited by a simple grid ring; both
the pixel set and the ring are carried explicitly.  Mattes are the conservative
discrete approximations of connected open plane regions, so the development
needs operations that extend a matte to improve the approximation — and those
operations must preserve the ring's simplicity, which is why the ring is part of
the data rather than derived.

## Main definitions

* `MRLink` — the successor relation of a contour: the end vertex of one dart is
  the start vertex of the next.
* `gborder` — the border darts of a pixel set.
* `Matte` — a nonempty pixel set with a node-simple contour cycle tracing it.
* `pointMatte p` — the single-pixel matte.
* `Matte.Adj` — matte adjacency, via converse border darts.
* `isRingCycle_iff`, `IsRingCycle.rotate`, `isRingCycle_surgery` — the contour
  toolkit: a contour is a chain that closes up, closedness is invariant under
  rotation, and an initial segment may be replaced by any chain with the same
  endpoints.
* `CoarseIn` — within a region, membership in the matte depends only on the
  coarse pixel.
* `refineMatte` — the matte covering exactly the subpixels of a matte in the
  binary refinement of the grid, with `refineDisk` and `refineRing` its data;
  `refineMatte_coarseIn` says it is coarse everywhere.
* `ehex d`, `equad d` — the 3×2 and 2×2 blocks of pixels used to certify that a
  new pixel touches a matte along one or two sides.
* `Ext1Hex`, `ext1Matte` — extension by a pixel meeting the matte on exactly one
  side; `Ext2Quad`, `ext2Matte` — on exactly two consecutive sides.  Both have
  `extDisk m d = insert (halfg d) m.disk` as their pixel set.
* `MatteExtension`, `ExtendsIn` — chains of single-pixel extensions, and the
  statement that a matte can be extended inside a rectangle to cover a pixel.
* `ndart p` — the dart of the pixel `p` whose edge separates `p` from `gnode p`;
  its quadrant is exactly the coarse pixel of `p`.
* `coarse_extends_in` — the main extension theorem: a matte that is coarse in a
  rectangle and meets it can be extended, inside it, to any inset pixel.
* `extend_madj` — such an extension can be stopped just as it becomes adjacent
  to a second matte, so the two mattes share a border edge.
* `mcorner` — the corner metric measuring how far a matte is from covering the
  whole neighbourhood of a grid point; `refine_mcorner` decreases it by
  extending the refinement of the matte.

## References

Gonthier's `theories/proof/matte.v`.
-/

namespace FourColor

/-- The successor relation for a contour cycle: the end vertex of `d₁` is the
start vertex of `d₂`. -/
def MRLink (d₁ d₂ : GPoint) : Prop := end1g d₁ = end0g d₂

/-- A list traces a closed contour. -/
def IsRingCycle (r : GPoint → GPoint → Prop) (l : List GPoint) : Prop :=
  List.IsChain r (l ++ l.take 1)

/-- The border darts of a set of pixels: the pixel of `d` lies in the set and
the pixel across its edge does not. -/
def gborder (m : Finset GPoint) : Set GPoint :=
  {d | halfg d ∈ m ∧ halfg (gedge d) ∉ m}

/-- A simple grid polyomino: a nonempty pixel set together with the node-simple
cycle of darts tracing its counterclockwise border. -/
structure Matte where
  /-- The pixels covered. -/
  disk : Finset GPoint
  /-- The contour cycle of darts. -/
  ring : List GPoint
  /-- The matte is nonempty. -/
  disk_nonempty : disk.Nonempty
  /-- The ring is a closed contour. -/
  ring_cycle : IsRingCycle MRLink ring
  /-- The ring is node-simple: it visits each vertex once. -/
  ring_simple : (ring.map end0g).Nodup
  /-- The ring is exactly the border. -/
  mem_ring : ∀ d, d ∈ ring ↔ d ∈ gborder disk

namespace Matte

/-- A dart and its reverse are never both on the border. -/
theorem gedge_notMem_ring (m : Matte) {d : GPoint} (hd : d ∈ m.ring) :
    gedge d ∉ m.ring := by
  intro he
  have h1 := (m.mem_ring d).mp hd
  have h2 := (m.mem_ring _).mp he
  rw [gborder, Set.mem_setOf_eq, gedge2] at h2
  exact h1.2 h2.1

theorem ring_nodup (m : Matte) : m.ring.Nodup :=
  List.Nodup.of_map _ m.ring_simple

/-- Matte adjacency: their borders contain converse darts. -/
def Adj (m₁ m₂ : Matte) : Prop := ∃ d ∈ m₂.ring, gedge d ∈ m₁.ring

theorem adj_symm {m₁ m₂ : Matte} (h : Adj m₁ m₂) : Adj m₂ m₁ := by
  obtain ⟨d, hd, he⟩ := h
  exact ⟨gedge d, he, by rwa [gedge2]⟩

theorem adj_irrefl (m : Matte) : ¬ Adj m m := by
  rintro ⟨d, hd, he⟩
  exact m.gedge_notMem_ring hd he

end Matte

/-! ### The single-pixel matte -/

namespace PointMatte

variable (p : GPoint)

/-- The four darts of a single pixel, counterclockwise. -/
def ring : List GPoint :=
  [p + p, gface (p + p), gface (gface (p + p)), gface (gface (gface (p + p)))]

theorem mem_ring_iff (d : GPoint) : d ∈ ring p ↔ halfg d = p := by
  constructor
  · intro hd
    have hh : halfg (p + p) = p := halfg_double p
    simp only [ring, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact hh
    · rw [halfg_gface, hh]
    · rw [halfg_gface, halfg_gface, hh]
    · rw [halfg_gface, halfg_gface, halfg_gface, hh]
  · intro hd
    have hh : halfg (p + p) = p := halfg_double p
    obtain ⟨i, hi, hgi⟩ := exists_iter_gface (d₁ := p + p) (d₂ := d) (by rw [hh, hd])
    simp only [ring, List.mem_cons, List.not_mem_nil, or_false]
    match i, hi with
    | 0, _ => exact Or.inl (by simpa using hgi.symm)
    | 1, _ => exact Or.inr (Or.inl (by simpa [Function.iterate_succ_apply] using hgi.symm))
    | 2, _ => exact Or.inr (Or.inr (Or.inl (by
        simpa [Function.iterate_succ_apply] using hgi.symm)))
    | 3, _ => exact Or.inr (Or.inr (Or.inr (by
        simpa [Function.iterate_succ_apply] using hgi.symm)))

theorem ring_cycle : IsRingCycle MRLink (ring p) := by
  have h4 : gface (gface (gface (gface (p + p)))) = p + p := gface4 _
  simp only [IsRingCycle, ring, List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  refine List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_ (List.IsChain.cons_cons ?_
    (List.IsChain.cons_cons ?_ (List.isChain_singleton _))))
  · exact (end0g_gface _).symm
  · exact (end0g_gface _).symm
  · exact (end0g_gface _).symm
  · have h := end0g_gface (gface (gface (gface (p + p))))
    rw [h4] at h
    exact h.symm

theorem ring_simple : ((ring p).map end0g).Nodup := by
  have hlist : (ring p).map end0g
      = [(0 : GPoint), ccw 0, ccw (ccw 0), ccw (ccw (ccw 0))].map fun c => p + c := by
    simp only [ring, List.map_cons, List.map_nil, end0g, halfg_gface, oddg_gface,
      halfg_double, oddg_double]
  rw [hlist]
  exact List.Nodup.map (fun c c' hcc => add_left_cancel hcc) (by decide)

theorem ring_def (d : GPoint) : d ∈ ring p ↔ d ∈ gborder {p} := by
  rw [mem_ring_iff, gborder, Set.mem_setOf_eq, Finset.mem_singleton,
    Finset.mem_singleton]
  constructor
  · intro hd
    exact ⟨hd, fun hc => halfg_gedge_ne d (hc.trans hd.symm)⟩
  · exact fun h => h.1

end PointMatte

/-- The matte consisting of the single pixel `p`. -/
def pointMatte (p : GPoint) : Matte where
  disk := {p}
  ring := PointMatte.ring p
  disk_nonempty := Finset.singleton_nonempty p
  ring_cycle := PointMatte.ring_cycle p
  ring_simple := PointMatte.ring_simple p
  mem_ring := PointMatte.ring_def p

/-! ### More dart arithmetic

A handful of identities about `end0g`, `end1g` and `gedge` that the surgery
operations need; they complement the lemmas in `FourColor.Grid`.
-/

/-- The edge dart starts where its dart ends. -/
theorem end0g_gedge (d : GPoint) : end0g (gedge d) = end1g d := by
  rw [end0g, halfg_gedge, oddg_gedge, arcg, end1g]
  abel

/-- The edge dart ends where its dart starts. -/
theorem end1g_gedge (d : GPoint) : end1g (gedge d) = end0g d := by
  have h : ccw (ccw (ccw (oddg d))) - ccw (ccw (oddg d)) + ccw (oddg d) = oddg d := by
    obtain ⟨x, y⟩ := oddg d
    simp only [ccw, Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [end1g, halfg_gedge, oddg_gedge, arcg, end0g]
  rw [show halfg d - (ccw (ccw (oddg d)) - ccw (oddg d)) + ccw (ccw (ccw (oddg d)))
      = halfg d + (ccw (ccw (ccw (oddg d))) - ccw (ccw (oddg d)) + ccw (oddg d)) from by abel, h]

/-- Doubling the start vertex of a dart. -/
theorem end0g_add_end0g (d : GPoint) : end0g d + end0g d = d + oddg d := by
  calc end0g d + end0g d = halfg d + halfg d + oddg d + oddg d := by
        simp only [end0g]; abel
    _ = d + oddg d := by rw [halfgK]

/-- Doubling the end vertex of a dart. -/
theorem end1g_add_end1g (d : GPoint) : end1g d + end1g d = gface d + ccw (oddg d) := by
  rw [gface_eq, end1g]
  abel

/-- A quarter turn never fixes a unit-square corner. -/
theorem ccw_ne_self {c : GPoint} (hc : IsOddg c) : ccw c ≠ c := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> decide

/-- A half turn never fixes a unit-square corner. -/
theorem ccw2_ne_self {c : GPoint} (hc : IsOddg c) : ccw (ccw c) ≠ c := by
  obtain ⟨x, y⟩ := c
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> decide

/-- Coordinates of the edge dart. -/
theorem gedge_eq_coord (d : GPoint) :
    gedge d = (d.1 + 1 - 2 * (d.2 % 2), d.2 + 2 * (d.1 % 2) - 1) := by
  obtain ⟨a, b⟩ := d
  simp only [gedge, arcg, ccw, oddg, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> ring

/-- The midpoint (doubled) of the edge of a dart determines the dart up to
reversal. -/
theorem eq_or_eq_gedge_of_mid {d d' : GPoint}
    (h : d + ccw (oddg d) = d' + ccw (oddg d')) : d' = d ∨ d' = gedge d := by
  obtain ⟨a, b⟩ := d
  obtain ⟨a', b'⟩ := d'
  rw [gedge_eq_coord]
  simp only [ccw, oddg, Prod.mk_add_mk, Prod.mk.injEq] at h ⊢
  omega

/-- Vertices of darts and midpoints of edges of darts never coincide: the
former have both coordinates even, the latter exactly one. -/
theorem add_oddg_ne_add_ccw_oddg (d d' : GPoint) : d + oddg d ≠ d' + ccw (oddg d') := by
  obtain ⟨a, b⟩ := d
  obtain ⟨a', b'⟩ := d'
  simp only [oddg, ccw, Prod.mk_add_mk, ne_eq, Prod.mk.injEq, not_and]
  intro _
  omega

/-- Halving the difference of a unit-square corner and the unit vector of an
adjacent corner. -/
theorem halfg_sub_arcg_ccw_mem {c e : GPoint} (hc : IsOddg c) (he : IsOddg e)
    (h : e = c ∨ e = ccw c) : halfg (e - arcg (ccw c)) = -arcg (ccw c) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨s, t⟩ := e
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> rcases he with ⟨hs | hs, ht | ht⟩ <;>
    subst hx <;> subst hy <;> subst hs <;> subst ht <;> revert h <;> decide

/-- Halving the difference of a unit-square corner and the unit vector of a
non-adjacent corner. -/
theorem halfg_sub_arcg_ccw_notMem {c e : GPoint} (hc : IsOddg c) (he : IsOddg e)
    (h : ¬(e = c ∨ e = ccw c)) : halfg (e - arcg (ccw c)) = 0 := by
  obtain ⟨x, y⟩ := c
  obtain ⟨s, t⟩ := e
  rcases hc with ⟨hx | hx, hy | hy⟩ <;> rcases he with ⟨hs | hs, ht | ht⟩ <;>
    subst hx <;> subst hy <;> subst hs <;> subst ht <;> revert h <;> decide

/-- The coarse pixel across the edge of a dart, computed from the coarse pixel
of the dart. -/
theorem halfg_halfg_gedge (q : GPoint) :
    halfg (halfg (gedge q))
      = halfg (halfg q) + halfg (oddg (halfg q) - arcg (ccw (oddg q))) := by
  have h : halfg (gedge q)
      = halfg (halfg q) + halfg (halfg q) + (oddg (halfg q) - arcg (ccw (oddg q))) := by
    rw [halfg_gedge, show halfg (halfg q) + halfg (halfg q)
        + (oddg (halfg q) - arcg (ccw (oddg q)))
      = halfg (halfg q) + halfg (halfg q) + oddg (halfg q) - arcg (ccw (oddg q)) from by abel,
      halfgK]
  rw [h, halfg_add_self]

/-! ### Contour cycles

A closed contour is a chain that links back to its start.  The `l ++ l.take 1`
formulation of `IsRingCycle` is convenient to state; the characterisation below
is what the proofs use.
-/

/-- A list is a closed contour exactly when it is a chain whose last element
links back to its first. -/
theorem isRingCycle_iff (r : GPoint → GPoint → Prop) (l : List GPoint) :
    IsRingCycle r l ↔ List.IsChain r l ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, r x y := by
  have hh : (l.take 1).head? = l.head? := by cases l <;> simp
  have hc : List.IsChain r (l.take 1) := by cases l <;> simp
  rw [IsRingCycle, List.isChain_append, hh]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hc, h.2⟩⟩

/-! #### Option-valued endpoints -/

/-- Reading off the last element from `getLast?`. -/
theorem eq_of_mem_getLast? {α : Type*} {l : List α} {x : α} (hne : l ≠ [])
    (h : x ∈ l.getLast?) : x = l.getLast hne := by
  have h' : l.getLast? = some x := h
  rw [List.getLast?_eq_some_getLast hne] at h'
  exact (Option.some_inj.mp h').symm

/-- Reading off the first element from `head?`. -/
theorem eq_of_mem_head? {α : Type*} {l : List α} {x : α} (hne : l ≠ [])
    (h : x ∈ l.head?) : x = l.head hne := by
  have h' : l.head? = some x := h
  rw [List.head?_eq_some_head hne] at h'
  exact (Option.some_inj.mp h').symm

/-- The last element belongs to `getLast?`. -/
theorem getLast_mem_getLast? {α : Type*} {l : List α} (hne : l ≠ []) :
    l.getLast hne ∈ l.getLast? := by
  rw [List.getLast?_eq_some_getLast hne]; rfl

/-- The first element belongs to `head?`. -/
theorem head_mem_head? {α : Type*} {l : List α} (hne : l ≠ []) :
    l.head hne ∈ l.head? := by
  rw [List.head?_eq_some_head hne]; rfl

/-- A closed contour stays closed after a one-step rotation. -/
theorem IsRingCycle.rotate_one {r : GPoint → GPoint → Prop} {l : List GPoint}
    (h : IsRingCycle r l) : IsRingCycle r (l.rotate 1) := by
  cases l with
  | nil => simpa using h
  | cons a t =>
    cases t with
    | nil => simpa using h
    | cons b t =>
      rw [isRingCycle_iff] at h
      obtain ⟨hchain, hclose⟩ := h
      have hab : r a b := hchain.rel_head? (by simp)
      have hlast : ((a :: b :: t) : List GPoint).getLast?
          = ((b :: t) : List GPoint).getLast? := by simp
      rw [show ((a :: b :: t) : List GPoint).rotate 1 = (b :: t) ++ [a] by simp,
        isRingCycle_iff]
      refine ⟨List.IsChain.append hchain.tail (List.isChain_singleton (R := r) a) ?_, ?_⟩
      · intro x hx y hy
        obtain rfl : a = y := by simpa using hy
        exact hclose x (hlast ▸ hx) a (by simp)
      · intro x hx y hy
        rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil a [])] at hx
        obtain rfl : a = x := by simpa using hx
        obtain rfl : b = y := by simpa using hy
        exact hab

/-- A closed contour stays closed after any rotation. -/
theorem IsRingCycle.rotate {r : GPoint → GPoint → Prop} {l : List GPoint}
    (h : IsRingCycle r l) (n : ℕ) : IsRingCycle r (l.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate l n 1]
    exact ih.rotate_one

/-- Being a closed contour is invariant under rotation. -/
theorem isRingCycle_rotate_iff {r : GPoint → GPoint → Prop} {l : List GPoint} {n : ℕ} :
    IsRingCycle r (l.rotate n) ↔ IsRingCycle r l := by
  refine ⟨fun h => ?_, fun h => h.rotate n⟩
  obtain ⟨m, hm⟩ := List.IsRotated.forall l n
  exact hm ▸ h.rotate m

/-- Every element of a list is the head of some rotation of it. -/
theorem exists_rotate_eq_cons {α : Type*} {l : List α} {x : α} (hx : x ∈ l) :
    ∃ (n : ℕ) (t : List α), l.rotate n = x :: t := by
  obtain ⟨s, u, rfl⟩ := List.append_of_mem hx
  exact ⟨s.length, u ++ s, by rw [List.rotate_append_length_eq]; rfl⟩

/-- Contour surgery: replacing an initial segment `s` of a closed contour by a
nonempty chain `u` with the same endpoints again yields a closed contour. -/
theorem isRingCycle_surgery {r : GPoint → GPoint → Prop} {s u t : List GPoint}
    (hs : s ≠ []) (hu : u ≠ []) (hcu : List.IsChain r u)
    (hstart : ∀ x, r x (s.head hs) → r x (u.head hu))
    (hend : ∀ y, r (s.getLast hs) y → r (u.getLast hu) y)
    (h : IsRingCycle r (s ++ t)) : IsRingCycle r (u ++ t) := by
  rw [isRingCycle_iff] at h ⊢
  obtain ⟨hchain, hclose⟩ := h
  have hct : List.IsChain r t := hchain.right_of_append
  refine ⟨List.IsChain.append hcu hct ?_, ?_⟩
  · intro x hx y hy
    have ht : t ≠ [] := by rintro rfl; simp at hy
    rw [eq_of_mem_getLast? hu hx, eq_of_mem_head? ht hy]
    exact hend _ (hchain.rel_getLast_head_of_append hs ht)
  · intro x hx y hy
    rw [List.head?_append_of_ne_nil _ hu] at hy
    rw [eq_of_mem_head? hu hy]
    rcases eq_or_ne t [] with rfl | ht
    · rw [List.append_nil] at hx
      rw [eq_of_mem_getLast? hu hx]
      refine hend _ (hstart _ (hclose _ ?_ _ ?_))
      · rw [List.append_nil]; exact getLast_mem_getLast? hs
      · rw [List.append_nil]; exact head_mem_head? hs
    · rw [List.getLast?_append_of_ne_nil _ ht] at hx
      have hx' : x ∈ (s ++ t).getLast? := by
        rw [List.getLast?_append_of_ne_nil _ ht]; exact hx
      have hy' : s.head hs ∈ (s ++ t).head? := by
        rw [List.head?_append_of_ne_nil _ hs]; exact head_mem_head? hs
      exact hstart x (hclose x hx' _ hy')

/-! ### Flattening helpers -/

/-- A flattened map that does nothing. -/
theorem flatten_map_eq_self {α : Type*} {l : List α} {F : α → List α}
    (h : ∀ y ∈ l, F y = [y]) : (l.map F).flatten = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.flatten_cons, h a List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy), List.singleton_append]

/-- Membership in a flattened map. -/
theorem mem_flatten_map {α β : Type*} {F : α → List β} {l : List α} {q : β} :
    q ∈ (l.map F).flatten ↔ ∃ a ∈ l, q ∈ F a := by
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨s, ⟨a, ha, rfl⟩, hq⟩; exact ⟨a, ha, hq⟩
  · rintro ⟨a, ha, hq⟩; exact ⟨F a, ⟨a, ha, rfl⟩, hq⟩

/-- The head of a flattened map of two-element lists. -/
theorem head?_flatten_map_pair {α β : Type*} (g h : α → β) (l : List α) :
    ((l.map fun a => [g a, h a]).flatten).head? = l.head?.map g := by
  cases l <;> simp

/-- The last element of a flattened map of two-element lists. -/
theorem getLast?_flatten_map_pair {α β : Type*} (g h : α → β) (l : List α) :
    ((l.map fun a => [g a, h a]).flatten).getLast? = l.getLast?.map h := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton t z ih =>
    simp

/-- A flattened map of two-element lists, up to permutation. -/
theorem perm_flatten_map_pair {α β : Type*} (g h : α → β) (l : List α) :
    List.Perm (l.map fun a => [g a, h a]).flatten (l.map g ++ l.map h) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.flatten_cons, List.cons_append]
    exact List.Perm.cons _ ((ih.cons (h a)).trans List.perm_middle.symm)

/-! ### Coarse regions -/

/-- Within `r` the matte is the binary refinement of a coarser region:
membership depends only on the coarse pixel. -/
def CoarseIn (r : Set GPoint) (m : Matte) : Prop :=
  ∀ p ∈ r, ∀ q, halfg q = halfg p → (q ∈ m.disk ↔ p ∈ m.disk)

/-! ### Grid refinement

Refining the grid replaces each pixel by its four subpixels; a coarse border
dart becomes two consecutive subpixel border darts, `rdart0` and `rdart1`.
-/

/-- The first of the two subpixel darts refining a coarse border dart. -/
def rdart0 (d : GPoint) : GPoint := d + d + oddg d

/-- The second of the two subpixel darts refining a coarse border dart. -/
def rdart1 (d : GPoint) : GPoint := gface d + gface d + oddg d

@[simp] theorem halfg_rdart0 (d : GPoint) : halfg (rdart0 d) = d := halfg_eq (oddgP d)

@[simp] theorem oddg_rdart0 (d : GPoint) : oddg (rdart0 d) = oddg d := oddg_eq (oddgP d)

@[simp] theorem halfg_rdart1 (d : GPoint) : halfg (rdart1 d) = gface d := halfg_eq (oddgP d)

@[simp] theorem oddg_rdart1 (d : GPoint) : oddg (rdart1 d) = oddg d := oddg_eq (oddgP d)

theorem end0g_rdart0 (d : GPoint) : end0g (rdart0 d) = d + oddg d := by
  rw [end0g, halfg_rdart0, oddg_rdart0]

theorem end1g_rdart0 (d : GPoint) : end1g (rdart0 d) = d + ccw (oddg d) := by
  rw [end1g, halfg_rdart0, oddg_rdart0]

theorem end0g_rdart1 (d : GPoint) : end0g (rdart1 d) = d + ccw (oddg d) := by
  rw [end0g, halfg_rdart1, oddg_rdart1, gface, arcg]
  abel

theorem end1g_rdart1 (d : GPoint) : end1g (rdart1 d) = gface d + ccw (oddg d) := by
  rw [end1g, halfg_rdart1, oddg_rdart1]

/-- The start vertex of `rdart0 d` is the doubled start vertex of `d`. -/
theorem end0g_rdart0_double (d : GPoint) : end0g (rdart0 d) = end0g d + end0g d := by
  rw [end0g_rdart0, end0g_add_end0g]

/-- The end vertex of `rdart1 d` is the doubled end vertex of `d`. -/
theorem end1g_rdart1_double (d : GPoint) : end1g (rdart1 d) = end1g d + end1g d := by
  rw [end1g_rdart1, end1g_add_end1g]

/-- The two subpixel darts of a coarse dart are consecutive. -/
theorem mrlink_rdart (d : GPoint) : MRLink (rdart0 d) (rdart1 d) := by
  rw [MRLink, end1g_rdart0, end0g_rdart1]

/-- Refinement preserves the successor relation across coarse darts. -/
theorem mrlink_rdart1_rdart0 {d d' : GPoint} (h : MRLink d d') :
    MRLink (rdart1 d) (rdart0 d') := by
  have h' : end1g d = end0g d' := h
  rw [MRLink, end1g_rdart1_double, end0g_rdart0_double, h']

/-- The pixels of the refinement of a pixel set: the four subpixels of each. -/
def refineDisk (s : Finset GPoint) : Finset GPoint :=
  s.biUnion fun p => (PointMatte.ring p).toFinset

@[simp] theorem mem_refineDisk {s : Finset GPoint} {q : GPoint} :
    q ∈ refineDisk s ↔ halfg q ∈ s := by
  simp only [refineDisk, Finset.mem_biUnion, List.mem_toFinset, PointMatte.mem_ring_iff]
  exact ⟨fun ⟨_, hp, hq⟩ => hq ▸ hp, fun h => ⟨halfg q, h, rfl⟩⟩

/-- The contour of the refinement: each coarse dart splits in two. -/
def refineRing (l : List GPoint) : List GPoint :=
  (l.map fun d => [rdart0 d, rdart1 d]).flatten

theorem mem_refineRing {l : List GPoint} {q : GPoint} :
    q ∈ refineRing l ↔ ∃ d ∈ l, oddg q = oddg d ∧ (halfg q = d ∨ halfg q = gface d) := by
  rw [refineRing, mem_flatten_map]
  constructor
  · rintro ⟨d, hd, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨d, hd, by simp, Or.inl (by simp)⟩
    · exact ⟨d, hd, by simp, Or.inr (by simp)⟩
  · rintro ⟨d, hd, hc, hp⟩
    refine ⟨d, hd, ?_⟩
    rcases hp with hp | hp
    · have h : rdart0 d = q := by rw [rdart0, ← hc, ← hp, halfgK]
      simp [h]
    · have h : rdart1 d = q := by rw [rdart1, ← hc, ← hp, halfgK]
      simp [h]

theorem refineRing_chain {l : List GPoint} (h : List.IsChain MRLink l) :
    List.IsChain MRLink (refineRing l) := by
  have hnil : [] ∉ l.map fun d => [rdart0 d, rdart1 d] := by simp
  rw [refineRing]
  refine (List.isChain_flatten hnil).mpr ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hs
    exact List.IsChain.cons_cons (mrlink_rdart d) (List.isChain_singleton _)
  · rw [List.isChain_map]
    refine h.imp fun a b hab x hx y hy => ?_
    obtain rfl : rdart1 a = x := by simpa using hx
    obtain rfl : rdart0 b = y := by simpa using hy
    exact mrlink_rdart1_rdart0 hab

theorem refineRing_cycle {l : List GPoint} (h : IsRingCycle MRLink l) :
    IsRingCycle MRLink (refineRing l) := by
  rw [isRingCycle_iff] at h ⊢
  obtain ⟨hchain, hclose⟩ := h
  refine ⟨refineRing_chain hchain, ?_⟩
  intro x hx y hy
  rcases eq_or_ne l [] with rfl | hne
  · rw [refineRing] at hx; simp at hx
  · rw [refineRing, getLast?_flatten_map_pair, List.getLast?_eq_some_getLast hne] at hx
    rw [refineRing, head?_flatten_map_pair, List.head?_eq_some_head hne] at hy
    obtain rfl : rdart1 (l.getLast hne) = x := by simpa using hx
    obtain rfl : rdart0 (l.head hne) = y := by simpa using hy
    exact mrlink_rdart1_rdart0
      (hclose _ (getLast_mem_getLast? hne) _ (head_mem_head? hne))

theorem refineRing_simple (m : Matte) : ((refineRing m.ring).map end0g).Nodup := by
  have hsplit : (refineRing m.ring).map end0g
      = (m.ring.map fun d => [end0g (rdart0 d), end0g (rdart1 d)]).flatten := by
    simp [refineRing, List.map_flatten, List.map_map, Function.comp_def]
  rw [hsplit]
  refine ((perm_flatten_map_pair (fun d => end0g (rdart0 d))
    (fun d => end0g (rdart1 d)) m.ring).nodup_iff).mpr ?_
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · have hmap : (m.ring.map fun d => end0g (rdart0 d))
        = (m.ring.map end0g).map fun v => v + v := by
      rw [List.map_map]
      exact List.map_congr_left fun d _ => end0g_rdart0_double d
    rw [hmap]
    refine List.Nodup.map ?_ m.ring_simple
    intro v w hvw
    obtain ⟨a, b⟩ := v
    obtain ⟨a', b'⟩ := w
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hvw ⊢
    omega
  · refine List.Nodup.map_on ?_ m.ring_nodup
    intro d hd d' hd' hEq
    rw [end0g_rdart1, end0g_rdart1] at hEq
    rcases eq_or_eq_gedge_of_mid hEq with h | h
    · exact h.symm
    · exact absurd (h ▸ hd') (m.gedge_notMem_ring hd)
  · intro v hv w hw hvw
    obtain ⟨d, -, hd⟩ := List.mem_map.mp hv
    obtain ⟨d', -, hd'⟩ := List.mem_map.mp hw
    refine add_oddg_ne_add_ccw_oddg d d' ?_
    rw [← end0g_rdart0, ← end0g_rdart1, hd, hd', hvw]

/-- The coarse pixel across the edge of a refined border dart. -/
theorem halfg_halfg_gedge_of_refine {q d : GPoint}
    (hc : oddg q = oddg d) (hp : halfg q = d ∨ halfg q = gface d) :
    halfg (halfg (gedge q)) = halfg (gedge d) := by
  have h1 : oddg (halfg q) = oddg d ∨ oddg (halfg q) = ccw (oddg d) := by
    rcases hp with hp | hp
    · exact Or.inl (by rw [hp])
    · exact Or.inr (by rw [hp, oddg_gface])
  have h2 : halfg (halfg q) = halfg d := by
    rcases hp with hp | hp
    · rw [hp]
    · rw [hp, halfg_gface]
  have h3 : IsOddg (oddg (halfg q)) := oddgP (halfg q)
  have key : halfg (oddg (halfg q) - arcg (ccw (oddg q))) = -arcg (ccw (oddg d)) := by
    rw [hc]
    exact halfg_sub_arcg_ccw_mem (oddgP d) h3 h1
  rw [halfg_halfg_gedge, key, h2, halfg_gedge]
  abel

theorem refineRing_def (m : Matte) (q : GPoint) :
    q ∈ refineRing m.ring ↔ q ∈ gborder (refineDisk m.disk) := by
  simp only [gborder, Set.mem_setOf_eq, mem_refineDisk, mem_refineRing]
  constructor
  · rintro ⟨d, hd, hc, hp⟩
    obtain ⟨hd1, hd2⟩ := (m.mem_ring d).mp hd
    refine ⟨?_, ?_⟩
    · rcases hp with hp | hp
      · rw [hp]; exact hd1
      · rw [hp, halfg_gface]; exact hd1
    · rw [halfg_halfg_gedge_of_refine hc hp]; exact hd2
  · rintro ⟨h1, h2⟩
    have hne : halfg (halfg (gedge q)) ≠ halfg (halfg q) := fun hh => h2 (hh ▸ h1)
    have hcond : oddg (halfg q) = oddg q ∨ oddg (halfg q) = ccw (oddg q) := by
      by_contra hcon
      exact hne (by
        rw [halfg_halfg_gedge,
          halfg_sub_arcg_ccw_notMem (oddgP q) (oddgP (halfg q)) hcon, add_zero])
    have hval : halfg (halfg (gedge q))
        = halfg (halfg q) - arcg (ccw (oddg q)) := by
      rw [halfg_halfg_gedge,
        halfg_sub_arcg_ccw_mem (oddgP q) (oddgP (halfg q)) hcond]
      abel
    refine ⟨halfg (halfg q) + halfg (halfg q) + oddg q, ?_, ?_, ?_⟩
    · rw [m.mem_ring]
      refine ⟨?_, ?_⟩
      · rw [halfg_eq (oddgP q)]; exact h1
      · rw [halfg_gedge, halfg_eq (oddgP q), oddg_eq (oddgP q), ← hval]; exact h2
    · rw [oddg_eq (oddgP q)]
    · have hk : halfg q = halfg (halfg q) + halfg (halfg q) + oddg (halfg q) :=
        (halfgK (halfg q)).symm
      rcases hcond with hcond | hcond
      · exact Or.inl (hk.trans (by rw [hcond]))
      · refine Or.inr (hk.trans ?_)
        rw [gface_eq, halfg_eq (oddgP q), oddg_eq (oddgP q), hcond]

/-- The refinement of a matte: it covers exactly the subpixels of its pixels in
the binary refinement of the grid. -/
def refineMatte (m : Matte) : Matte where
  disk := refineDisk m.disk
  ring := refineRing m.ring
  disk_nonempty := by
    obtain ⟨p, hp⟩ := m.disk_nonempty
    exact ⟨p + p, by rw [mem_refineDisk, halfg_double]; exact hp⟩
  ring_cycle := refineRing_cycle m.ring_cycle
  ring_simple := refineRing_simple m
  mem_ring := refineRing_def m

@[simp] theorem mem_refineMatte {m : Matte} {q : GPoint} :
    q ∈ (refineMatte m).disk ↔ halfg q ∈ m.disk := mem_refineDisk

/-- A refined matte is coarse everywhere. -/
theorem refineMatte_coarseIn (m : Matte) (r : Set GPoint) : CoarseIn r (refineMatte m) := by
  intro p _ q hq
  rw [mem_refineMatte, mem_refineMatte, hq]

/-! ### Extension neighbourhoods

`ehex d` is the 3×2 block of pixels made of the pixel of `d` together with the
five pixels adjacent to it in the half-plane left of `d`; `equad d` is the 2×2
block left of both `d` and `gface d`.
-/

/-- The 3×2 block of pixels around the pixel of `d`, left of `d`. -/
def ehex (d : GPoint) : GRect := gchopRect (gtouch (halfg d)) d

/-- The 2×2 block of pixels left of both `d` and `gface d`. -/
def equad (d : GPoint) : GRect := gchopRect (ehex d) (gface d)

theorem mem_ehex (d p : GPoint) :
    p ∈ (ehex d).toRegion ↔ p ∈ (gtouch (halfg d)).toRegion ∧ p ∈ gchop d :=
  mem_gchopRect _ _ _

theorem mem_equad (d p : GPoint) :
    p ∈ (equad d).toRegion ↔
      p ∈ (gtouch (halfg d)).toRegion ∧ p ∈ gchop d ∧ p ∈ gchop (gface d) := by
  rw [equad, mem_gchopRect, mem_ehex, and_assoc]

/-- A pixel touches itself. -/
theorem mem_gtouch_self (p : GPoint) : p ∈ (gtouch p).toRegion := by
  simp only [gtouch, GRect.mem_toRegion]
  omega

/-- The pixel of a dart lies in its hexagon. -/
theorem halfg_mem_ehex (d : GPoint) : halfg d ∈ (ehex d).toRegion :=
  (mem_ehex d _).mpr ⟨mem_gtouch_self _, gchop_halfg d⟩

/-- The pixel of a dart lies in its quadrant. -/
theorem halfg_mem_equad (d : GPoint) : halfg d ∈ (equad d).toRegion :=
  (mem_equad d _).mpr ⟨mem_gtouch_self _, gchop_halfg d, by
    have h := gchop_halfg (gface d); rwa [halfg_gface] at h⟩

/-- The quadrant of `d` is contained in its hexagon. -/
theorem equad_subset_ehex (d : GPoint) : (equad d).toRegion ⊆ (ehex d).toRegion :=
  gchopRect_subset _ _

/-- The quadrant of `d` is contained in the hexagon of the next dart. -/
theorem equad_subset_ehex_gface (d : GPoint) :
    (equad d).toRegion ⊆ (ehex (gface d)).toRegion := by
  intro p hp
  rw [mem_equad] at hp
  rw [mem_ehex, halfg_gface]
  exact ⟨hp.1, hp.2.2⟩

/-- Every grid point adjacent to the start vertex of `d` lies, as a pixel, in
the quadrant of `gface d`. -/
theorem sub_end0g_mem_equad_gface {d e : GPoint} (he : IsOddg e) :
    end0g d - e ∈ (equad (gface d)).toRegion := by
  rw [mem_equad]
  obtain ⟨s, t⟩ := e
  rcases he with ⟨hs | hs, ht | ht⟩ <;> rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    subst hs <;> subst ht <;>
    simp [gtouch, gchop, end0g, halfg_gface, oddg_gface, ccw, hx, hy] <;> omega

/-- The start vertex of a dart lies, as a pixel, in the quadrant of the next
dart. -/
theorem end0g_mem_equad_gface (d : GPoint) : end0g d ∈ (equad (gface d)).toRegion := by
  have h := sub_end0g_mem_equad_gface (d := d) (e := 0) ⟨Or.inl rfl, Or.inl rfl⟩
  rwa [sub_zero] at h

/-- If the matte avoids the quadrant of `gface d`, the start vertex of `d` is
not a pixel of the matte. -/
theorem end0g_notMem_disk {m : Matte} {d : GPoint}
    (h : ∀ p ∈ m.disk, p ∉ (equad (gface d)).toRegion) : end0g d ∉ m.disk :=
  fun hd => h _ hd (end0g_mem_equad_gface d)

/-- If the matte avoids the quadrant of `gface d`, the start vertex of `d` is
not a vertex of the contour. -/
theorem end0g_notMem_map_end0g {m : Matte} {d : GPoint}
    (h : ∀ p ∈ m.disk, p ∉ (equad (gface d)).toRegion) :
    end0g d ∉ m.ring.map end0g := by
  intro hmem
  obtain ⟨d₁, hd₁, hE⟩ := List.mem_map.mp hmem
  have hh : halfg d₁ = end0g d - oddg d₁ := by
    rw [← hE, end0g]; abel
  exact h (halfg d₁) ((m.mem_ring d₁).mp hd₁).1
    (hh ▸ sub_end0g_mem_equad_gface (oddgP d₁))

/-- The pixel across the edge of `gface d` lies in the hexagon of `d`. -/
theorem halfg_gedge_gface_mem_ehex (d : GPoint) :
    halfg (gedge (gface d)) ∈ (ehex d).toRegion := by
  rw [mem_ehex]
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [halfg_gedge, halfg_gface, oddg_gface, gtouch, gchop, arcg, ccw, hx, hy] <;> omega

/-- The pixel across the edge of `gface (gface d)` lies in the hexagon of `d`. -/
theorem halfg_gedge_gface2_mem_ehex (d : GPoint) :
    halfg (gedge (gface (gface d))) ∈ (ehex d).toRegion := by
  rw [mem_ehex]
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [halfg_gedge, halfg_gface, oddg_gface, gtouch, gchop, arcg, ccw, hx, hy] <;> omega

/-- The pixel across the edge of `gface (gface (gface d))` lies in the hexagon
of `d`. -/
theorem halfg_gedge_gface3_mem_ehex (d : GPoint) :
    halfg (gedge (gface (gface (gface d)))) ∈ (ehex d).toRegion := by
  rw [mem_ehex]
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [halfg_gedge, halfg_gface, oddg_gface, gtouch, gchop, arcg, ccw, hx, hy] <;> omega

/-! ### Extending a matte by a pixel -/

/-- Two distinct border darts of a matte have distinct start vertices. -/
theorem Matte.end0g_inj (m : Matte) {x y : GPoint} (hx : x ∈ m.ring) (hy : y ∈ m.ring)
    (h : end0g x = end0g y) : x = y :=
  List.inj_on_of_nodup_map m.ring_simple hx hy h

/-- The disk of an extension: the pixel of `d` is added. -/
def extDisk (m : Matte) (d : GPoint) : Finset GPoint := insert (halfg d) m.disk

@[simp] theorem mem_extDisk {m : Matte} {d p : GPoint} :
    p ∈ extDisk m d ↔ p = halfg d ∨ p ∈ m.disk := Finset.mem_insert

/-- Replacing the single occurrence of `x` in a list by a list `u`. -/
theorem flatten_map_replace {α : Type*} [DecidableEq α] {A B : List α} {x : α} {u : List α}
    (hA : x ∉ A) (hB : x ∉ B) :
    ((A ++ x :: B).map fun y => if y = x then u else [y]).flatten = A ++ u ++ B := by
  have hA' : ∀ y ∈ A, (if y = x then u else [y]) = [y] := fun y hy => by
    have hne : y ≠ x := fun hyx => hA (hyx ▸ hy)
    simp [hne]
  have hB' : ∀ y ∈ B, (if y = x then u else [y]) = [y] := fun y hy => by
    have hne : y ≠ x := fun hyx => hB (hyx ▸ hy)
    simp [hne]
  rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons,
    flatten_map_eq_self hA', flatten_map_eq_self hB']
  simp

/-- `d` faces the matte across its edge and its hexagon is otherwise free, so
adding the pixel of `d` glues it to the matte along exactly one side. -/
structure Ext1Hex (m : Matte) (d : GPoint) : Prop where
  /-- The pixel across the edge of `d` is in the matte. -/
  mem_disk : halfg (gedge d) ∈ m.disk
  /-- No pixel of the matte lies in the hexagon of `d`. -/
  free : ∀ p ∈ m.disk, p ∉ (ehex d).toRegion

namespace Ext1Hex

/-- The new pixel is not already in the matte. -/
theorem halfg_notMem {m : Matte} {d : GPoint} (h : Ext1Hex m d) : halfg d ∉ m.disk :=
  fun hd => h.free _ hd (halfg_mem_ehex d)

/-- The edge dart of `d` is a border dart of the matte. -/
theorem gedge_mem_ring {m : Matte} {d : GPoint} (h : Ext1Hex m d) : gedge d ∈ m.ring :=
  (m.mem_ring _).mpr ⟨h.mem_disk, by rw [gedge2]; exact h.halfg_notMem⟩

theorem gedge_gface_notMem {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    halfg (gedge (gface d)) ∉ m.disk :=
  fun hp => h.free _ hp (halfg_gedge_gface_mem_ehex d)

theorem gedge_gface2_notMem {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    halfg (gedge (gface (gface d))) ∉ m.disk :=
  fun hp => h.free _ hp (halfg_gedge_gface2_mem_ehex d)

theorem gedge_gface3_notMem {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    halfg (gedge (gface (gface (gface d)))) ∉ m.disk :=
  fun hp => h.free _ hp (halfg_gedge_gface3_mem_ehex d)

theorem free_equad {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    ∀ p ∈ m.disk, p ∉ (equad d).toRegion :=
  fun p hp hq => h.free p hp (equad_subset_ehex d hq)

theorem free_equad_gface3 {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    ∀ p ∈ m.disk, p ∉ (equad (gface (gface (gface d)))).toRegion := by
  intro p hp hq
  have hsub := equad_subset_ehex_gface (gface (gface (gface d))) hq
  rw [gface4] at hsub
  exact h.free p hp hsub

end Ext1Hex

/-! #### Start vertices along the new pixel -/

theorem end0g_gface_eq (d : GPoint) : end0g (gface d) = halfg d + ccw (oddg d) := by
  rw [end0g, halfg_gface, oddg_gface]

theorem end0g_gface2_eq (d : GPoint) :
    end0g (gface (gface d)) = halfg d + ccw (ccw (oddg d)) := by
  rw [end0g, halfg_gface, halfg_gface, oddg_gface, oddg_gface]

theorem end0g_gface3_eq (d : GPoint) :
    end0g (gface (gface (gface d))) = halfg d + ccw (ccw (ccw (oddg d))) := by
  rw [end0g, halfg_gface, halfg_gface, halfg_gface, oddg_gface, oddg_gface, oddg_gface]

theorem end0g_gface_ne_gface2 (d : GPoint) :
    end0g (gface d) ≠ end0g (gface (gface d)) := by
  rw [end0g_gface_eq, end0g_gface2_eq]
  exact fun hc => ccw_ne_self (isOddg_ccw (oddgP d)) (add_left_cancel hc).symm

theorem end0g_gface_ne_gface3 (d : GPoint) :
    end0g (gface d) ≠ end0g (gface (gface (gface d))) := by
  rw [end0g_gface_eq, end0g_gface3_eq]
  exact fun hc => ccw2_ne_self (isOddg_ccw (oddgP d)) (add_left_cancel hc).symm

theorem end0g_gface2_ne_gface3 (d : GPoint) :
    end0g (gface (gface d)) ≠ end0g (gface (gface (gface d))) := by
  rw [end0g_gface2_eq, end0g_gface3_eq]
  exact fun hc =>
    ccw_ne_self (isOddg_ccw (isOddg_ccw (oddgP d))) (add_left_cancel hc).symm

/-- The last of the three new darts ends where `d` starts. -/
theorem end1g_gface3 (d : GPoint) : end1g (gface (gface (gface d))) = end0g d := by
  rw [← end0g_gface, gface4]

/-! #### The one-sided extension -/

/-- The contour of a one-sided extension: the border dart `gedge d` is replaced
by the three other darts of the new pixel. -/
def ext1Ring (m : Matte) (d : GPoint) : List GPoint :=
  (m.ring.map fun x =>
    if x = gedge d then [gface d, gface (gface d), gface (gface (gface d))]
    else [x]).flatten

theorem mem_ext1Ring {m : Matte} {d : GPoint} (hd : gedge d ∈ m.ring) (q : GPoint) :
    q ∈ ext1Ring m d ↔
      (q = gface d ∨ q = gface (gface d) ∨ q = gface (gface (gface d)))
        ∨ (q ∈ m.ring ∧ q ≠ gedge d) := by
  rw [ext1Ring, mem_flatten_map]
  constructor
  · rintro ⟨x, hx, hq⟩
    split_ifs at hq with hxe
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      exact Or.inl hq
    · simp only [List.mem_singleton] at hq
      subst hq
      exact Or.inr ⟨hx, hxe⟩
  · rintro (hq | ⟨hq, hne⟩)
    · exact ⟨gedge d, hd, by simpa using hq⟩
    · exact ⟨q, hq, by simp [hne]⟩

theorem ext1Ring_eq {m : Matte} {d : GPoint} {A B : List GPoint}
    (hA : m.ring = A ++ gedge d :: B) :
    ext1Ring m d = A ++ [gface d, gface (gface d), gface (gface (gface d))] ++ B := by
  have hnd : (A ++ gedge d :: B).Nodup := hA ▸ m.ring_nodup
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  have hA' : gedge d ∉ A := fun hmem => hdisj _ hmem _ List.mem_cons_self rfl
  have hB' : gedge d ∉ B := (List.nodup_cons.mp hnd2).1
  rw [ext1Ring, hA, flatten_map_replace hA' hB']

theorem ext1Ring_cycle {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    IsRingCycle MRLink (ext1Ring m d) := by
  obtain ⟨A, B, hA⟩ := List.append_of_mem h.gedge_mem_ring
  have hrot : (ext1Ring m d).rotate A.length
      = [gface d, gface (gface d), gface (gface (gface d))] ++ (B ++ A) := by
    rw [ext1Ring_eq hA, List.append_assoc, List.rotate_append_length_eq, List.append_assoc]
  have hrot' : m.ring.rotate A.length = [gedge d] ++ (B ++ A) := by
    rw [hA, List.rotate_append_length_eq]
    rfl
  rw [← isRingCycle_rotate_iff (n := A.length), hrot]
  refine isRingCycle_surgery (s := [gedge d]) (by simp) (by simp) ?_ ?_ ?_
    (hrot' ▸ m.ring_cycle.rotate A.length)
  · exact List.IsChain.cons_cons (end0g_gface (gface d)).symm
      (List.IsChain.cons_cons (end0g_gface (gface (gface d))).symm
        (List.isChain_singleton _))
  · intro x hx
    have hx' : end1g x = end0g (gedge d) := hx
    change end1g x = end0g (gface d)
    rw [hx', end0g_gedge, end0g_gface]
  · intro y hy
    have hy' : end1g (gedge d) = end0g y := hy
    exact (end1g_gface3 d).trans ((end1g_gedge d).symm.trans hy')

theorem ext1Ring_simple {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    ((ext1Ring m d).map end0g).Nodup := by
  obtain ⟨A, B, hA⟩ := List.append_of_mem h.gedge_mem_ring
  have hrot : (ext1Ring m d).rotate A.length
      = [gface d, gface (gface d), gface (gface (gface d))] ++ (B ++ A) := by
    rw [ext1Ring_eq hA, List.append_assoc, List.rotate_append_length_eq, List.append_assoc]
  have hrot' : m.ring.rotate A.length = gedge d :: (B ++ A) := by
    rw [hA, List.rotate_append_length_eq]
    rfl
  have hsub : ∀ x ∈ B ++ A, x ∈ m.ring := by
    intro x hx
    rw [← List.mem_rotate (n := A.length), hrot']
    exact List.mem_cons_of_mem _ hx
  have hmsimple : (end0g (gedge d) :: (B ++ A).map end0g).Nodup := by
    have hs := m.ring_simple
    rw [← List.nodup_rotate (n := A.length), ← List.map_rotate, hrot'] at hs
    exact hs
  rw [List.nodup_cons] at hmsimple
  obtain ⟨hnotmem, htnodup⟩ := hmsimple
  refine (List.nodup_rotate (n := A.length)).mp ?_
  rw [← List.map_rotate, hrot, List.map_append, List.nodup_append]
  refine ⟨?_, htnodup, ?_⟩
  · simp [end0g_gface_ne_gface2 d, end0g_gface_ne_gface3 d, end0g_gface2_ne_gface3 d]
  · intro v hv w hw hvw
    have hw' : w ∈ m.ring.map end0g := by
      obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hw
      exact List.mem_map.mpr ⟨x, hsub x hx, hxw⟩
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl
    · refine hnotmem ?_
      have heq : end0g (gedge d) = end0g (gface d) := by rw [end0g_gedge, end0g_gface]
      rw [heq, hvw]
      exact hw
    · refine end0g_notMem_map_end0g h.free_equad_gface3 ?_
      rw [hvw]
      exact hw'
    · have hfree : ∀ p ∈ m.disk,
          p ∉ (equad (gface (gface (gface (gface d))))).toRegion := by
        rw [gface4]
        exact h.free_equad
      refine end0g_notMem_map_end0g hfree ?_
      rw [hvw]
      exact hw'

theorem ext1Ring_def {m : Matte} {d : GPoint} (h : Ext1Hex m d) (q : GPoint) :
    q ∈ ext1Ring m d ↔ q ∈ gborder (extDisk m d) := by
  rw [mem_ext1Ring h.gedge_mem_ring, gborder, Set.mem_setOf_eq, mem_extDisk, mem_extDisk]
  constructor
  · rintro (hq | ⟨hq, hne⟩)
    · have hhq : halfg q = halfg d := by
        rcases hq with rfl | rfl | rfl
        · rw [halfg_gface]
        · rw [halfg_gface, halfg_gface]
        · rw [halfg_gface, halfg_gface, halfg_gface]
      refine ⟨Or.inl hhq, ?_⟩
      rintro (he | he)
      · exact halfg_gedge_ne q (he.trans hhq.symm)
      · rcases hq with rfl | rfl | rfl
        · exact h.gedge_gface_notMem he
        · exact h.gedge_gface2_notMem he
        · exact h.gedge_gface3_notMem he
    · obtain ⟨h1, h2⟩ := (m.mem_ring q).mp hq
      refine ⟨Or.inr h1, ?_⟩
      rintro (he | he)
      · obtain ⟨i, hi, hgi⟩ := exists_iter_gface (d₁ := d) (d₂ := gedge q) he.symm
        have hqe : q = gedge (gface^[i] d) := by rw [hgi, gedge2]
        match i, hi with
        | 0, _ =>
          rw [Function.iterate_zero_apply] at hqe
          exact hne hqe
        | 1, _ =>
          rw [show gface^[1] d = gface d by simp] at hqe
          exact h.gedge_gface_notMem (hqe ▸ h1)
        | 2, _ =>
          rw [show gface^[2] d = gface (gface d) by
            simp [Function.iterate_succ_apply]] at hqe
          exact h.gedge_gface2_notMem (hqe ▸ h1)
        | 3, _ =>
          rw [show gface^[3] d = gface (gface (gface d)) by
            simp [Function.iterate_succ_apply]] at hqe
          exact h.gedge_gface3_notMem (hqe ▸ h1)
      · exact h2 he
  · rintro ⟨h1, h2⟩
    rw [not_or] at h2
    obtain ⟨h2a, h2b⟩ := h2
    rcases h1 with h1 | h1
    · obtain ⟨i, hi, hgi⟩ := exists_iter_gface (d₁ := d) (d₂ := q) h1.symm
      match i, hi with
      | 0, _ =>
        rw [Function.iterate_zero_apply] at hgi
        exact absurd (hgi ▸ h.mem_disk) h2b
      | 1, _ =>
        rw [show gface^[1] d = gface d by simp] at hgi
        exact Or.inl (Or.inl hgi.symm)
      | 2, _ =>
        rw [show gface^[2] d = gface (gface d) by simp [Function.iterate_succ_apply]] at hgi
        exact Or.inl (Or.inr (Or.inl hgi.symm))
      | 3, _ =>
        rw [show gface^[3] d = gface (gface (gface d)) by
          simp [Function.iterate_succ_apply]] at hgi
        exact Or.inl (Or.inr (Or.inr hgi.symm))
    · refine Or.inr ⟨(m.mem_ring q).mpr ⟨h1, h2b⟩, ?_⟩
      rintro rfl
      exact h2a (by rw [gedge2])

/-- The matte obtained by adding the pixel of `d`, which touches the matte on
exactly one side. -/
def ext1Matte {m : Matte} {d : GPoint} (h : Ext1Hex m d) : Matte where
  disk := extDisk m d
  ring := ext1Ring m d
  disk_nonempty := ⟨halfg d, Finset.mem_insert_self _ _⟩
  ring_cycle := ext1Ring_cycle h
  ring_simple := ext1Ring_simple h
  mem_ring := ext1Ring_def h

@[simp] theorem disk_ext1Matte {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    (ext1Matte h).disk = insert (halfg d) m.disk := rfl

@[simp] theorem ring_ext1Matte {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    (ext1Matte h).ring = ext1Ring m d := rfl

/-! ### Extending a matte along two sides -/

/-- The pixel across the edge of `gface (gface d)` lies in the quadrant of
`d`. -/
theorem halfg_gedge_gface2_mem_equad (d : GPoint) :
    halfg (gedge (gface (gface d))) ∈ (equad d).toRegion := by
  rw [mem_equad]
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [halfg_gedge, halfg_gface, oddg_gface, gtouch, gchop, arcg, ccw, hx, hy] <;> omega

/-- The pixel across the edge of `gface (gface (gface d))` lies in the quadrant
of `d`. -/
theorem halfg_gedge_gface3_mem_equad (d : GPoint) :
    halfg (gedge (gface (gface (gface d)))) ∈ (equad d).toRegion := by
  rw [mem_equad]
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [halfg_gedge, halfg_gface, oddg_gface, gtouch, gchop, arcg, ccw, hx, hy] <;> omega

/-- Consecutive darts of a pixel have distinct edge darts. -/
theorem gedge_gface_ne_gedge (d : GPoint) : gedge (gface d) ≠ gedge d := by
  intro hc
  have hd : gface d = d := by
    have := congrArg gedge hc
    rwa [gedge2, gedge2] at this
  exact ccw_ne_self (oddgP d) (by rw [← oddg_gface, hd])

/-- Rotating a flattened map. -/
theorem flatten_map_rotate {α β : Type*} (F : α → List β) (A C : List α) :
    (((A ++ C).rotate A.length).map F).flatten
      = (((A ++ C).map F).flatten).rotate ((A.map F).flatten).length := by
  rw [List.rotate_append_length_eq, List.map_append, List.flatten_append, List.map_append,
    List.flatten_append, List.rotate_append_length_eq]

/-- In a contour, a dart whose start vertex follows the end vertex of `x` is the
immediate successor of `x`. -/
theorem exists_cons_cons_of_ring {m : Matte} {x y : GPoint} {u : List GPoint}
    (hR : IsRingCycle MRLink (x :: u)) (hsub : ∀ z ∈ x :: u, z ∈ m.ring)
    (hx : x ∈ m.ring) (hy : y ∈ m.ring) (hxy : x ≠ y)
    (hlink : end1g x = end0g y) : ∃ t, u = y :: t := by
  rw [isRingCycle_iff] at hR
  cases u with
  | nil =>
    exact absurd (m.end0g_inj hy hx (by
      have hcl := hR.2 x (by simp) x (by simp)
      have hcl' : end1g x = end0g x := hcl
      rw [← hlink, hcl'])) (Ne.symm hxy)
  | cons d₁ t =>
    refine ⟨t, ?_⟩
    have hd₁ : MRLink x d₁ := hR.1.rel_head? (by simp)
    have hd₁' : end1g x = end0g d₁ := hd₁
    have : y = d₁ := m.end0g_inj hy (hsub d₁ (by simp)) (by rw [← hlink, hd₁'])
    rw [this]

/-- Two adjacent border darts of the matte around a common new pixel occur
consecutively in the contour. -/
theorem exists_rotate_ext2 {m : Matte} {d : GPoint}
    (h1 : gedge d ∈ m.ring) (h2 : gedge (gface d) ∈ m.ring) :
    ∃ (A C t : List GPoint), m.ring = A ++ C ∧
      C ++ A = gedge (gface d) :: gedge d :: t := by
  obtain ⟨A, t₀, hA⟩ := List.append_of_mem h2
  have hrot : m.ring.rotate A.length = gedge (gface d) :: (t₀ ++ A) := by
    rw [hA, List.rotate_append_length_eq]
    rfl
  have hcyc : IsRingCycle MRLink (gedge (gface d) :: (t₀ ++ A)) :=
    hrot ▸ m.ring_cycle.rotate A.length
  have hsub : ∀ z ∈ gedge (gface d) :: (t₀ ++ A), z ∈ m.ring := by
    intro z hz
    rw [← hrot] at hz
    exact List.mem_rotate.mp hz
  have hlink : end1g (gedge (gface d)) = end0g (gedge d) := by
    rw [end1g_gedge, end0g_gedge, end0g_gface]
  obtain ⟨t, ht⟩ :=
    exists_cons_cons_of_ring hcyc hsub h2 h1 (gedge_gface_ne_gedge d) hlink
  exact ⟨A, gedge (gface d) :: t₀, t, hA, by rw [List.cons_append, ht]⟩

/-- `d` faces the matte across the edges of both `d` and `gface d`, and its
quadrant is otherwise free. -/
structure Ext2Quad (m : Matte) (d : GPoint) : Prop where
  /-- The pixel across the edge of `d` is in the matte. -/
  mem_disk : halfg (gedge d) ∈ m.disk
  /-- The pixel across the edge of `gface d` is in the matte. -/
  mem_disk_gface : halfg (gedge (gface d)) ∈ m.disk
  /-- No pixel of the matte lies in the quadrant of `d`. -/
  free : ∀ p ∈ m.disk, p ∉ (equad d).toRegion

namespace Ext2Quad

/-- The new pixel is not already in the matte. -/
theorem halfg_notMem {m : Matte} {d : GPoint} (h : Ext2Quad m d) : halfg d ∉ m.disk :=
  fun hd => h.free _ hd (halfg_mem_equad d)

theorem gedge_mem_ring {m : Matte} {d : GPoint} (h : Ext2Quad m d) : gedge d ∈ m.ring :=
  (m.mem_ring _).mpr ⟨h.mem_disk, by rw [gedge2]; exact h.halfg_notMem⟩

theorem gedge_gface_mem_ring {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    gedge (gface d) ∈ m.ring :=
  (m.mem_ring _).mpr ⟨h.mem_disk_gface, by
    rw [gedge2, halfg_gface]; exact h.halfg_notMem⟩

theorem gedge_gface2_notMem {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    halfg (gedge (gface (gface d))) ∉ m.disk :=
  fun hp => h.free _ hp (halfg_gedge_gface2_mem_equad d)

theorem gedge_gface3_notMem {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    halfg (gedge (gface (gface (gface d)))) ∉ m.disk :=
  fun hp => h.free _ hp (halfg_gedge_gface3_mem_equad d)

end Ext2Quad

/-- The darts replacing a border dart in a two-sided extension: the two border
darts along the new pixel disappear and two new ones take their place. -/
def ext2Darts (d x : GPoint) : List GPoint :=
  if x = gedge (gface d) then [gface (gface d), gface (gface (gface d))]
  else if x = gedge d then [] else [x]

/-- The contour of a two-sided extension. -/
def ext2Ring (m : Matte) (d : GPoint) : List GPoint :=
  (m.ring.map (ext2Darts d)).flatten

theorem mem_ext2Ring {m : Matte} {d : GPoint} (h2 : gedge (gface d) ∈ m.ring)
    (q : GPoint) :
    q ∈ ext2Ring m d ↔
      (q = gface (gface d) ∨ q = gface (gface (gface d)))
        ∨ (q ∈ m.ring ∧ q ≠ gedge (gface d) ∧ q ≠ gedge d) := by
  rw [ext2Ring, mem_flatten_map]
  constructor
  · rintro ⟨x, hx, hq⟩
    rw [ext2Darts] at hq
    split_ifs at hq with hx1 hx2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      exact Or.inl hq
    · simp at hq
    · simp only [List.mem_singleton] at hq
      subst hq
      exact Or.inr ⟨hx, hx1, hx2⟩
  · rintro (hq | ⟨hq, hn1, hn2⟩)
    · exact ⟨gedge (gface d), h2, by rw [ext2Darts]; simpa using hq⟩
    · exact ⟨q, hq, by rw [ext2Darts]; simp [hn1, hn2]⟩

theorem ext2Ring_rotate {m : Matte} {d : GPoint} {A C t : List GPoint}
    (hAC : m.ring = A ++ C) (hCA : C ++ A = gedge (gface d) :: gedge d :: t) :
    (ext2Ring m d).rotate ((A.map (ext2Darts d)).flatten).length
      = [gface (gface d), gface (gface (gface d))] ++ t := by
  have hnd : (C ++ A).Nodup :=
    (List.perm_append_comm (l₁ := A) (l₂ := C)).nodup (hAC ▸ m.ring_nodup)
  rw [hCA, List.nodup_cons, List.nodup_cons] at hnd
  have ht : ∀ z ∈ t, ext2Darts d z = [z] := by
    intro z hz
    have hz1 : z ≠ gedge (gface d) := fun hc =>
      hnd.1 (by rw [hc] at hz; exact List.mem_cons_of_mem _ hz)
    have hz2 : z ≠ gedge d := fun hc => hnd.2.1 (by rw [hc] at hz; exact hz)
    rw [ext2Darts]
    simp [hz1, hz2]
  have hflat : ((gedge (gface d) :: gedge d :: t).map (ext2Darts d)).flatten
      = [gface (gface d), gface (gface (gface d))] ++ t := by
    rw [List.map_cons, List.flatten_cons, List.map_cons, List.flatten_cons,
      flatten_map_eq_self ht]
    rw [ext2Darts, ext2Darts]
    simp [(gedge_gface_ne_gedge d).symm]
  rw [ext2Ring, hAC, ← flatten_map_rotate, List.rotate_append_length_eq, hCA, hflat]

section Ext2

theorem ext2Ring_cycle {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    IsRingCycle MRLink (ext2Ring m d) := by
  obtain ⟨A, C, t, hAC, hCA⟩ :=
    exists_rotate_ext2 h.gedge_mem_ring h.gedge_gface_mem_ring
  have hrot := ext2Ring_rotate hAC hCA
  have hmrot : m.ring.rotate A.length = [gedge (gface d), gedge d] ++ t := by
    rw [hAC, List.rotate_append_length_eq, hCA]
    rfl
  rw [← isRingCycle_rotate_iff (n := ((A.map (ext2Darts d)).flatten).length), hrot]
  refine isRingCycle_surgery (s := [gedge (gface d), gedge d]) (by simp) (by simp) ?_ ?_ ?_
    (hmrot ▸ m.ring_cycle.rotate A.length)
  · exact List.IsChain.cons_cons (end0g_gface (gface (gface d))).symm
      (List.isChain_singleton _)
  · intro x hx
    have hx' : end1g x = end0g (gedge (gface d)) := hx
    change end1g x = end0g (gface (gface d))
    rw [hx', end0g_gedge, end0g_gface]
  · intro y hy
    have hy' : end1g (gedge d) = end0g y := hy
    exact (end1g_gface3 d).trans ((end1g_gedge d).symm.trans hy')

theorem ext2Ring_simple {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    ((ext2Ring m d).map end0g).Nodup := by
  obtain ⟨A, C, t, hAC, hCA⟩ :=
    exists_rotate_ext2 h.gedge_mem_ring h.gedge_gface_mem_ring
  have hrot := ext2Ring_rotate hAC hCA
  have hmrot : m.ring.rotate A.length = gedge (gface d) :: gedge d :: t := by
    rw [hAC, List.rotate_append_length_eq, hCA]
  have hsub : ∀ x ∈ t, x ∈ m.ring := by
    intro x hx
    rw [← List.mem_rotate (n := A.length), hmrot]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
  have hmsimple : ((gedge (gface d) :: gedge d :: t).map end0g).Nodup := by
    have hs := m.ring_simple
    rw [← List.nodup_rotate (n := A.length), ← List.map_rotate, hmrot] at hs
    exact hs
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hmsimple
  obtain ⟨⟨-, hne1⟩, -, htnodup⟩ := hmsimple
  refine (List.nodup_rotate (n := ((A.map (ext2Darts d)).flatten).length)).mp ?_
  rw [← List.map_rotate, hrot, List.map_append, List.nodup_append]
  refine ⟨by simp [end0g_gface2_ne_gface3 d], htnodup, ?_⟩
  intro v hv w hw hvw
  have hw' : w ∈ m.ring.map end0g := by
    obtain ⟨x, hx, hxw⟩ := List.mem_map.mp hw
    exact List.mem_map.mpr ⟨x, hsub x hx, hxw⟩
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases hv with rfl | rfl
  · refine hne1 ?_
    have heq : end0g (gedge (gface d)) = end0g (gface (gface d)) := by
      rw [end0g_gedge, end0g_gface]
    rw [heq, hvw]
    exact hw
  · have hfree : ∀ p ∈ m.disk, p ∉ (equad (gface (gface (gface (gface d))))).toRegion := by
      rw [gface4]
      exact h.free
    refine end0g_notMem_map_end0g hfree ?_
    rw [hvw]
    exact hw'

theorem ext2Ring_def {m : Matte} {d : GPoint} (h : Ext2Quad m d) (q : GPoint) :
    q ∈ ext2Ring m d ↔ q ∈ gborder (extDisk m d) := by
  rw [mem_ext2Ring h.gedge_gface_mem_ring, gborder, Set.mem_setOf_eq,
    mem_extDisk, mem_extDisk]
  constructor
  · rintro (hq | ⟨hq, hn1, hn2⟩)
    · have hhq : halfg q = halfg d := by
        rcases hq with rfl | rfl
        · rw [halfg_gface, halfg_gface]
        · rw [halfg_gface, halfg_gface, halfg_gface]
      refine ⟨Or.inl hhq, ?_⟩
      rintro (he | he)
      · exact halfg_gedge_ne q (he.trans hhq.symm)
      · rcases hq with rfl | rfl
        · exact h.gedge_gface2_notMem he
        · exact h.gedge_gface3_notMem he
    · obtain ⟨h1, h2⟩ := (m.mem_ring q).mp hq
      refine ⟨Or.inr h1, ?_⟩
      rintro (he | he)
      · obtain ⟨i, hi, hgi⟩ := exists_iter_gface (d₁ := d) (d₂ := gedge q) he.symm
        have hqe : q = gedge (gface^[i] d) := by rw [hgi, gedge2]
        match i, hi with
        | 0, _ =>
          rw [Function.iterate_zero_apply] at hqe
          exact hn2 hqe
        | 1, _ =>
          rw [show gface^[1] d = gface d by simp] at hqe
          exact hn1 hqe
        | 2, _ =>
          rw [show gface^[2] d = gface (gface d) by
            simp [Function.iterate_succ_apply]] at hqe
          exact h.gedge_gface2_notMem (hqe ▸ h1)
        | 3, _ =>
          rw [show gface^[3] d = gface (gface (gface d)) by
            simp [Function.iterate_succ_apply]] at hqe
          exact h.gedge_gface3_notMem (hqe ▸ h1)
      · exact h2 he
  · rintro ⟨h1, h2⟩
    rw [not_or] at h2
    obtain ⟨h2a, h2b⟩ := h2
    rcases h1 with h1 | h1
    · obtain ⟨i, hi, hgi⟩ := exists_iter_gface (d₁ := d) (d₂ := q) h1.symm
      match i, hi with
      | 0, _ =>
        rw [Function.iterate_zero_apply] at hgi
        exact absurd (hgi ▸ h.mem_disk) h2b
      | 1, _ =>
        rw [show gface^[1] d = gface d by simp] at hgi
        exact absurd (hgi ▸ h.mem_disk_gface) h2b
      | 2, _ =>
        rw [show gface^[2] d = gface (gface d) by simp [Function.iterate_succ_apply]] at hgi
        exact Or.inl (Or.inl hgi.symm)
      | 3, _ =>
        rw [show gface^[3] d = gface (gface (gface d)) by
          simp [Function.iterate_succ_apply]] at hgi
        exact Or.inl (Or.inr hgi.symm)
    · refine Or.inr ⟨(m.mem_ring q).mpr ⟨h1, h2b⟩, ?_, ?_⟩
      · rintro rfl
        exact h2a (by rw [gedge2, halfg_gface])
      · rintro rfl
        exact h2a (by rw [gedge2])

/-- The matte obtained by adding the pixel of `d`, which touches the matte on
exactly two consecutive sides. -/
def ext2Matte {m : Matte} {d : GPoint} (h : Ext2Quad m d) : Matte where
  disk := extDisk m d
  ring := ext2Ring m d
  disk_nonempty := ⟨halfg d, Finset.mem_insert_self _ _⟩
  ring_cycle := ext2Ring_cycle h
  ring_simple := ext2Ring_simple h
  mem_ring := ext2Ring_def h

@[simp] theorem disk_ext2Matte {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    (ext2Matte h).disk = insert (halfg d) m.disk := rfl

@[simp] theorem ring_ext2Matte {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    (ext2Matte h).ring = ext2Ring m d := rfl

end Ext2

/-! ### Chains of extensions -/

/-- `MatteExtension m xm` says there is a chain of mattes from `m` to `xm`, each
obtained from the previous one by adding a single adjacent pixel. -/
inductive MatteExtension (m : Matte) : Matte → Prop
  /-- The empty chain. -/
  | refl : MatteExtension m m
  /-- One more pixel, glued along the border dart `gedge d`. -/
  | step {d : GPoint} {xm₀ xm : Matte} (h : MatteExtension m xm₀)
      (hd : gedge d ∈ xm₀.ring) (hxm : ∀ p, p ∈ xm.disk ↔ p ∈ extDisk xm₀ d) :
      MatteExtension m xm

/-- An extension covers the matte it extends. -/
theorem MatteExtension.subset {m xm : Matte} (h : MatteExtension m xm) :
    ∀ p ∈ m.disk, p ∈ xm.disk := by
  induction h with
  | refl => exact fun _ hp => hp
  | step _ _ hxm ih =>
    exact fun p hp => (hxm p).mpr (mem_extDisk.mpr (Or.inr (ih p hp)))

/-- Extensions compose. -/
theorem MatteExtension.trans {m xm ym : Matte} (h : MatteExtension m xm)
    (h' : MatteExtension xm ym) : MatteExtension m ym := by
  induction h' with
  | refl => exact h
  | step _ hd hxm ih => exact MatteExtension.step ih hd hxm

/-- A one-sided extension is an extension. -/
theorem matteExtension_ext1Matte {m : Matte} {d : GPoint} (h : Ext1Hex m d) :
    MatteExtension m (ext1Matte h) :=
  MatteExtension.step MatteExtension.refl h.gedge_mem_ring fun _ => Iff.rfl

/-- A two-sided extension is an extension. -/
theorem matteExtension_ext2Matte {m : Matte} {d : GPoint} (h : Ext2Quad m d) :
    MatteExtension m (ext2Matte h) :=
  MatteExtension.step MatteExtension.refl h.gedge_mem_ring fun _ => Iff.rfl

/-- `m` can be extended inside `r` so as to cover the pixel `p`. -/
def ExtendsIn (m : Matte) (r : Set GPoint) (p : GPoint) : Prop :=
  ∃ xm : Matte, MatteExtension m xm ∧ (∀ q ∈ xm.disk, q ∈ r ∨ q ∈ m.disk) ∧ p ∈ xm.disk

theorem ExtendsIn.mono {m : Matte} {r₁ r₂ : Set GPoint} (hr : r₁ ⊆ r₂) {p : GPoint}
    (h : ExtendsIn m r₁ p) : ExtendsIn m r₂ p := by
  obtain ⟨xm, hx, hsub, hp⟩ := h
  exact ⟨xm, hx, fun q hq => (hsub q hq).imp (fun hq' => hr hq') id, hp⟩

/-- A pixel already in the matte needs no extension. -/
theorem extendsIn_of_mem {m : Matte} {r : Set GPoint} {p : GPoint} (hp : p ∈ m.disk) :
    ExtendsIn m r p :=
  ⟨m, MatteExtension.refl, fun _ hq => Or.inr hq, hp⟩

/-! ### The outward dart of a pixel

`ndart q` is the dart of the pixel `q` whose edge separates `q` from its node
neighbour `gnode q`.  Its quadrant `equad (ndart q)` is exactly the block of
four pixels sharing the coarse pixel of `q`, which is what makes it the right
dart to probe a coarse matte with.
-/

/-- The dart of the pixel `q` whose edge separates `q` from `gnode q`. -/
def ndart (q : GPoint) : GPoint := q + q + ccw (ccw (ccw (oddg q)))

@[simp] theorem halfg_ndart (q : GPoint) : halfg (ndart q) = q :=
  halfg_eq (isOddg_ccw (isOddg_ccw (isOddg_ccw (oddgP q))))

@[simp] theorem oddg_ndart (q : GPoint) : oddg (ndart q) = ccw (ccw (ccw (oddg q))) :=
  oddg_eq (isOddg_ccw (isOddg_ccw (isOddg_ccw (oddgP q))))

@[simp] theorem halfg_gedge_ndart (q : GPoint) : halfg (gedge (ndart q)) = gnode q := by
  rw [halfg_gedge, halfg_ndart, oddg_ndart, ccw4, gnode_def]

/-- Crossing the edge of the next dart of `ndart q` is again an outward dart. -/
theorem gedge_gface_ndart (q : GPoint) :
    gedge (gface (ndart q)) = ndart (gface (gedge q)) := by
  have ho : oddg (gface (ndart q)) = oddg q := by rw [oddg_gface, oddg_ndart, ccw4]
  have hh : halfg (gface (ndart q)) = q := by rw [halfg_gface, halfg_ndart]
  have hX : gface (gedge q) = q - arcg (ccw (oddg q)) := by
    rw [gface_def, oddg_gedge, arcg_ccw2 (oddgP q), gedge_def]
    abel
  have hodd : oddg (gface (gedge q)) = ccw (ccw (ccw (oddg q))) := by
    rw [oddg_gface, oddg_gedge]
  rw [gedge_eq, hh, ho, ndart, hodd, hX, ccw4 (ccw (ccw (oddg q)))]

/-- The outward dart of `gnode q`, turned once, crosses back into `q`. -/
theorem gedge_gface_ndart_gnode (q : GPoint) :
    gedge (gface (ndart (gnode q))) = ndart q := by
  rw [gedge_gface_ndart, gface_gedge_gnode]

theorem gface_ndart_gnode (q : GPoint) : gface (ndart (gnode q)) = gedge (ndart q) := by
  rw [← gedge_gface_ndart_gnode q, gedge2]

/-- Reading the outward dart off the pixel it points into. -/
theorem ndart_halfg_gedge_gface_ndart (q : GPoint) :
    ndart (halfg (gedge (gface (ndart q)))) = gedge (gface (ndart q)) := by
  rw [gedge_gface_ndart, halfg_ndart]

/-- The quadrant of `ndart q` consists of the pixels with the same coarse pixel
as `q`. -/
theorem halfg_of_mem_equad_ndart {q z : GPoint}
    (h : z ∈ (equad (ndart q)).toRegion) : halfg z = halfg q := by
  rw [mem_equad, halfg_ndart] at h
  suffices hs : z.1 / 2 = q.1 / 2 ∧ z.2 / 2 = q.2 / 2 by
    simp only [halfg, Prod.ext_iff]
    exact hs
  have hox : (oddg q).1 = q.1 % 2 := rfl
  have hoy : (oddg q).2 = q.2 % 2 := rfl
  have hx := (oddgP q).1
  have hy := (oddgP q).2
  rw [hox] at hx
  rw [hoy] at hy
  revert h
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [gtouch, gchop, halfg_gface, oddg_gface, oddg_ndart, halfg_ndart, ccw,
      hox, hoy, hx, hy] <;> omega

/-- Two hexagons that straddle a common edge are covered by the two
corresponding quadrants. -/
theorem mem_equad_or_of_mem_ehex {d z : GPoint}
    (h : z ∈ (ehex d).toRegion ∨ z ∈ (ehex (gface (gedge (gface d)))).toRegion) :
    z ∈ (equad d).toRegion ∨ z ∈ (equad (gedge (gface d))).toRegion := by
  simp only [mem_ehex, mem_equad] at h ⊢
  revert h
  rcases oddgP d with ⟨hx | hx, hy | hy⟩ <;>
    simp [gtouch, gchop, halfg_gface, oddg_gface, halfg_gedge,
      oddg_gedge, arcg, ccw, hx, hy] <;> omega

/-! ### Extending inside a rectangle -/

/-- Auxiliary induction for `coarse_extends_in`.  The rectangle `r0` is where
the matte is known to be coarse and where `p` is inset; `r` is the rectangle,
shrinking along the induction on its area, inside which the extension is
built. -/
theorem coarseExtendsIn_aux (m : Matte) : ∀ n : ℕ, ∀ r r0 : GRect, ∀ p : GPoint,
    r.area ≤ n → (∃ q ∈ m.disk, q ∈ r.toRegion) → p ∈ r.toRegion →
    (∀ q, q ∈ r0.toRegion → q ∈ m.disk → q ∈ r.toRegion) →
    r.toRegion ⊆ r0.toRegion → p ∈ r0.inset.toRegion → CoarseIn r0.toRegion m →
    ExtendsIn m r.toRegion p := by
  intro n
  induction n with
  | zero =>
    intro r r0 p hn _ hrp _ _ _ _
    have hpos : 0 < r.area := (GRect.proper_iff_nonempty r).mpr ⟨p, hrp⟩
    omega
  | succ n ih =>
  intro r r0 p hn hmr hrp hrm0 hrr0 hr0p hcoarse
  by_cases hmp : p ∈ m.disk
  · exact extendsIn_of_mem hmp
  -- Gluing one pixel at `p` onto an extension living across the edge of `d`.
  have ext_hex : ∀ d : GPoint, halfg d = p → (∀ z ∈ m.disk, z ∉ (ehex d).toRegion) →
      ExtendsIn m (gchopRect r (gedge d)).toRegion (halfg (gedge d)) →
      ExtendsIn m r.toRegion p := by
    intro d hdp hfree hext
    obtain ⟨xm, hxm, hsub, hxed⟩ := hext
    have hext1 : Ext1Hex xm d := by
      refine ⟨hxed, ?_⟩
      intro z hz hze
      rcases hsub z hz with hc | hc
      · exact (gchop_gedge d z).mp ((mem_gchopRect r _ z).mp hc).2 ((mem_ehex d z).mp hze).2
      · exact hfree z hc hze
    refine ⟨ext1Matte hext1, hxm.trans (matteExtension_ext1Matte hext1), ?_, ?_⟩
    · intro z hz
      rw [disk_ext1Matte, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Or.inl (by rw [hdp]; exact hrp)
      · rcases hsub z hz with hc | hc
        · exact Or.inl (gchopRect_subset r _ hc)
        · exact Or.inr hc
    · rw [disk_ext1Matte, hdp]
      exact Finset.mem_insert_self _ _
  -- A pixel of the matte inside `r0` but outside the wide half-plane of a dart
  -- at `p` lets us chop `r` and recurse.
  have IHp : ∀ d : GPoint, halfg d = p →
      (∃ z ∈ m.disk, z ∈ r0.toRegion ∧ z ∉ gchop1 d) → ExtendsIn m r.toRegion p := by
    intro d hdp hz0
    obtain ⟨z0, hz0m, hz0r0, hz0c⟩ := hz0
    have hpchop : p ∈ gchop d := by rw [← hdp]; exact gchop_halfg d
    have hr01p : p ∈ (gchop1Rect r0 d).inset.toRegion := by
      rw [GRect.mem_inset_iff]
      intro w hw
      rw [mem_gchop1Rect]
      refine ⟨(GRect.mem_inset_iff r0 p).mp hr0p hw, ?_⟩
      have hw' : w ∈ (gtouch (halfg d)).toRegion := by rw [hdp]; exact hw
      exact ((mem_gtouch_iff_chop1 d w).mp hw').1
    by_cases hm01 : ∃ z ∈ m.disk, z ∈ (gchop1Rect r0 d).toRegion
    · obtain ⟨z1, hz1m, hz1⟩ := hm01
      rw [mem_gchop1Rect] at hz1
      have harea : (gchop1Rect r d).area < r.area :=
        area_lt_of_ssubset (fun w hw => ((mem_gchop1Rect r d w).mp hw).1)
          (hrm0 z0 hz0r0 hz0m) (fun hc => hz0c ((mem_gchop1Rect r d z0).mp hc).2)
      refine ExtendsIn.mono (fun w hw => ((mem_gchop1Rect r d w).mp hw).1)
        (ih (gchop1Rect r d) (gchop1Rect r0 d) p (by omega) ?_ ?_ ?_ ?_ hr01p ?_)
      · exact ⟨z1, hz1m, (mem_gchop1Rect r d z1).mpr ⟨hrm0 z1 hz1.1 hz1m, hz1.2⟩⟩
      · exact (mem_gchop1Rect r d p).mpr ⟨hrp, gchop_subset_gchop1 d hpchop⟩
      · intro w hw hwm
        rw [mem_gchop1Rect] at hw ⊢
        exact ⟨hrm0 w hw.1 hwm, hw.2⟩
      · intro w hw
        rw [mem_gchop1Rect] at hw ⊢
        exact ⟨hrr0 hw.1, hw.2⟩
      · intro w hw u hu
        exact hcoarse w (gchopRect_subset r0 _ hw) u hu
    · push_neg at hm01
      refine ext_hex d hdp ?_ ?_
      · intro w hwm hwe
        refine hm01 w hwm ((GRect.mem_inset_iff (gchop1Rect r0 d) p).mp hr01p ?_)
        have hgt := ((mem_ehex d w).mp hwe).1
        rwa [hdp] at hgt
      · have hm_r1 : ∃ w ∈ m.disk, w ∈ (gchopRect r (gedge d)).toRegion := by
          refine ⟨z0, hz0m, (mem_gchopRect r _ z0).mpr ⟨hrm0 z0 hz0r0 hz0m, ?_⟩⟩
          exact (gchop_gedge d z0).mpr fun hc => hz0c (gchop_subset_gchop1 d hc)
        have hpr1 : p ∉ (gchopRect r (gedge d)).toRegion := fun hc =>
          (gchop_gedge d p).mp ((mem_gchopRect r _ p).mp hc).2 hpchop
        have harea : (gchopRect r (gedge d)).area < r.area :=
          area_lt_of_ssubset (fun w hw => ((mem_gchopRect r _ w).mp hw).1) hrp hpr1
        obtain ⟨w0, hw0m, hw0⟩ := hm_r1
        refine ih (gchopRect r (gedge d)) r0 (halfg (gedge d)) (by omega)
          ⟨w0, hw0m, hw0⟩ ?_ ?_ ?_ ?_ hcoarse
        · refine mem_gchopRect_halfg ?_ hw0
          rw [gedge2, hdp]
          exact hrp
        · intro w hw hwm
          refine (mem_gchopRect r _ w).mpr ⟨hrm0 w hw hwm, ?_⟩
          refine (gchop_gedge d w).mpr fun hc => hm01 w hwm ?_
          exact (mem_gchop1Rect r0 d w).mpr ⟨hw, gchop_subset_gchop1 d hc⟩
        · intro w hw
          exact hrr0 ((mem_gchopRect r _ w).mp hw).1
        · refine mem_inset_gedge (by rw [hdp]; exact hr0p) ?_
          refine gchopRect_subset r0 (gedge (gface (gface (gedge d)))) ?_
          refine mem_gchopRect_halfg ?_
            ((mem_gchopRect r0 _ z0).mpr ⟨hz0r0, (gchop_gedge _ z0).mpr hz0c⟩)
          rw [gedge2, halfg_gface, halfg_gface]
          refine (GRect.mem_inset_iff r0 p).mp hr0p ?_
          have hgt := gtouch_gedge d
          rwa [hdp] at hgt
  -- The coarse structure of the matte around `p`.
  have hr0_p : p ∈ r0.toRegion := hrr0 hrp
  have m_nd4 : ∀ w, w ∈ r0.toRegion → ∀ z ∈ m.disk,
      z ∈ (equad (ndart w)).toRegion → w ∈ m.disk := fun w hw z hzm hz =>
    (hcoarse w hw z (halfg_of_mem_equad_ndart hz)).mp hzm
  have hr0_np : gnode p ∈ r0.toRegion := by
    refine (GRect.mem_inset_iff r0 p).mp hr0p ?_
    have h := gtouch_gedge (ndart p)
    rwa [halfg_gedge_ndart, halfg_ndart] at h
  have hp4 : ∀ z ∈ m.disk, z ∉ (equad (ndart p)).toRegion := fun z hzm hz =>
    hmp (m_nd4 p hr0_p z hzm hz)
  by_cases hp6 : ∃ z ∈ m.disk, z ∈ (ehex (ndart p)).toRegion
  · obtain ⟨z, hzm, hz6⟩ := hp6
    have hefp : halfg (gedge (gface (ndart p))) ∈ m.disk := by
      refine m_nd4 _ ?_ z hzm ?_
      · refine (GRect.mem_inset_iff r0 p).mp hr0p ?_
        have h := gtouch_gedge (gface (ndart p))
        rwa [halfg_gface, halfg_ndart] at h
      · rw [ndart_halfg_gedge_gface_ndart]
        rcases mem_equad_or_of_mem_ehex (d := ndart p) (Or.inl hz6) with h | h
        · exact absurd h (hp4 z hzm)
        · exact h
    by_cases hfp6 : ∃ w ∈ m.disk, w ∈ (ehex (gface (ndart p))).toRegion
    · obtain ⟨w, hwm, hw6⟩ := hfp6
      have hep : halfg (gedge (ndart p)) ∈ m.disk := by
        rw [halfg_gedge_ndart]
        refine m_nd4 _ hr0_np w hwm ?_
        have hin : w ∈ (ehex (gface (gedge (gface (ndart (gnode p)))))).toRegion := by
          rw [gedge_gface_ndart_gnode]
          exact hw6
        rcases mem_equad_or_of_mem_ehex (d := ndart (gnode p)) (Or.inr hin) with h | h
        · exact h
        · rw [gedge_gface_ndart_gnode] at h
          exact absurd h (hp4 w hwm)
      have hext2 : Ext2Quad m (ndart p) := ⟨hep, hefp, hp4⟩
      refine ⟨ext2Matte hext2, matteExtension_ext2Matte hext2, ?_, ?_⟩
      · intro u hu
        rw [disk_ext2Matte, Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [halfg_ndart]
          exact Or.inl hrp
        · exact Or.inr hu
      · rw [disk_ext2Matte, halfg_ndart]
        exact Finset.mem_insert_self _ _
    · push_neg at hfp6
      refine ext_hex (gface (ndart p)) (by rw [halfg_gface, halfg_ndart]) hfp6 ?_
      exact ⟨m, MatteExtension.refl, fun u hu => Or.inr hu, hefp⟩
  · push_neg at hp6
    by_cases hmp9 : ∃ z ∈ m.disk, z ∈ (gtouch p).toRegion
    · obtain ⟨z, hzm, hz9⟩ := hmp9
      refine ext_hex (ndart p) (halfg_ndart p) hp6 ?_
      by_cases hnd : gnode p ∈ m.disk
      · exact ⟨m, MatteExtension.refl, fun u hu => Or.inr hu,
          by rw [halfg_gedge_ndart]; exact hnd⟩
      · have hnd4 : ∀ w ∈ m.disk, w ∉ (equad (ndart (gnode p))).toRegion :=
          fun w hwm hw => hnd (m_nd4 _ hr0_np w hwm hw)
        have hr0_n2p : gnode (gnode p) ∈ r0.toRegion :=
          (GRect.mem_inset_iff r0 p).mp hr0p (gnode_gnode_mem_gtouch p)
        have hz9' : z ∈ (gtouch (halfg (ndart p))).toRegion := by
          rw [halfg_ndart]; exact hz9
        obtain ⟨hc0, hc1, hc2, hc3⟩ := (mem_gtouch_iff_chop1 (ndart p) z).mp hz9'
        have hep_z : z ∈ gchop (gedge (ndart p)) :=
          (gchop_gedge (ndart p) z).mpr fun hc =>
            hp6 z hzm ((mem_ehex (ndart p) z).mpr ⟨hz9', hc⟩)
        have hzt : z ∈ (gtouch (halfg (gedge (ndart p)))).toRegion := by
          rw [mem_gtouch_iff_chop1]
          refine ⟨gchop_subset_gchop1 _ hep_z, ?_, gchop_subset_gchop1 _ hc0, ?_⟩
          · have h := gchop1_shift (gface (gface (gface (ndart p))))
            rw [gface4] at h
            rw [h]
            exact hc3
          · rw [gchop1_gface3_gedge]
            exact hc1
        have hm_n2p : gnode (gnode p) ∈ m.disk := by
          refine m_nd4 _ hr0_n2p z hzm ?_
          have hin :
              z ∈ (ehex (gface (gedge (gface (ndart (gnode (gnode p))))))).toRegion := by
            rw [gedge_gface_ndart_gnode, gface_ndart_gnode, mem_ehex]
            exact ⟨hzt, hep_z⟩
          rcases mem_equad_or_of_mem_ehex (d := ndart (gnode (gnode p)))
            (Or.inr hin) with h | h
          · exact h
          · rw [gedge_gface_ndart_gnode] at h
            exact absurd h (hnd4 z hzm)
        have hr_np : gnode p ∈ r.toRegion :=
          mem_of_gnode_gnode hrp (hrm0 _ hr0_n2p hm_n2p)
        have hext1 : Ext1Hex m (ndart (gnode p)) := by
          refine ⟨by rw [halfg_gedge_ndart]; exact hm_n2p, ?_⟩
          intro w hwm hw
          rcases mem_equad_or_of_mem_ehex (d := ndart (gnode p)) (Or.inl hw) with h | h
          · exact hnd4 w hwm h
          · rw [gedge_gface_ndart_gnode] at h
            exact hp4 w hwm h
        refine ⟨ext1Matte hext1, matteExtension_ext1Matte hext1, ?_, ?_⟩
        · intro u hu
          rw [disk_ext1Matte, Finset.mem_insert] at hu
          rcases hu with rfl | hu
          · refine Or.inl ?_
            rw [halfg_ndart, mem_gchopRect]
            refine ⟨hr_np, ?_⟩
            have h := gchop_halfg (gedge (ndart p))
            rwa [halfg_gedge_ndart] at h
          · exact Or.inr hu
        · rw [disk_ext1Matte, halfg_ndart, halfg_gedge_ndart]
          exact Finset.mem_insert_self _ _
    · push_neg at hmp9
      obtain ⟨q1, hq1m, hq1r⟩ := hmr
      have hq1r0 : q1 ∈ r0.toRegion := hrr0 hq1r
      by_cases hA : q1 ∈ gchop1 (ndart p)
      · by_cases hB : q1 ∈ gchop1 (gface (ndart p))
        · by_cases hC : q1 ∈ gchop1 (gface (gface (ndart p)))
          · by_cases hD : q1 ∈ gchop1 (gface (gface (gface (ndart p))))
            · have h := (mem_gtouch_iff_chop1 (ndart p) q1).mpr ⟨hA, hB, hC, hD⟩
              rw [halfg_ndart] at h
              exact absurd h (hmp9 q1 hq1m)
            · exact IHp (gface (gface (gface (ndart p))))
                (by rw [halfg_gface, halfg_gface, halfg_gface, halfg_ndart])
                ⟨q1, hq1m, hq1r0, hD⟩
          · exact IHp (gface (gface (ndart p)))
              (by rw [halfg_gface, halfg_gface, halfg_ndart]) ⟨q1, hq1m, hq1r0, hC⟩
        · exact IHp (gface (ndart p)) (by rw [halfg_gface, halfg_ndart])
            ⟨q1, hq1m, hq1r0, hB⟩
      · exact IHp (ndart p) (halfg_ndart p) ⟨q1, hq1m, hq1r0, hA⟩

/-- A matte that is coarse in a rectangle `r` and meets `r` can be extended
inside `r` so as to cover any pixel inset in `r`. -/
theorem coarse_extends_in {m : Matte} {r : GRect} (hcoarse : CoarseIn r.toRegion m)
    (hmr : ∃ q ∈ m.disk, q ∈ r.toRegion) {p : GPoint} (hp : p ∈ r.inset.toRegion) :
    ExtendsIn m r.toRegion p :=
  coarseExtendsIn_aux m r.area r r p le_rfl hmr (GRect.mem_of_mem_inset hp)
    (fun _ hq _ => hq) (fun _ hq => hq) hp hcoarse

/-- Extending a matte that is coarse in `r` until it becomes adjacent to a
matte `m1` meeting the inset of `r`: the extension stays in `r ∪ m` and avoids
`m1` altogether. -/
theorem extend_madj {m m1 : Matte} {r : GRect} (hcoarse : CoarseIn r.toRegion m)
    (hmr : ∃ q ∈ m.disk, q ∈ r.toRegion) (hm1 : ∃ q ∈ m1.disk, q ∈ r.inset.toRegion)
    (hdisj : ∀ q ∈ m.disk, q ∉ m1.disk) :
    ∃ xm : Matte, (∀ q ∈ m.disk, q ∈ xm.disk) ∧
      (∀ q ∈ xm.disk, (q ∈ r.toRegion ∨ q ∈ m.disk) ∧ q ∉ m1.disk) ∧ Matte.Adj m1 xm := by
  obtain ⟨p, hp1, hpr⟩ := hm1
  obtain ⟨xm, hxm, hxsub, hxp⟩ := coarse_extends_in hcoarse hmr hpr
  have key : ∀ ym : Matte, MatteExtension m ym →
      (∀ q ∈ ym.disk, q ∈ r.toRegion ∨ q ∈ m.disk) → (∃ q ∈ m1.disk, q ∈ ym.disk) →
      ∃ zm : Matte, (∀ q ∈ m.disk, q ∈ zm.disk) ∧
        (∀ q ∈ zm.disk, (q ∈ r.toRegion ∨ q ∈ m.disk) ∧ q ∉ m1.disk) ∧
        Matte.Adj m1 zm := by
    intro ym hym
    induction hym with
    | refl =>
      intro _ hmeet
      obtain ⟨q, hq1, hqm⟩ := hmeet
      exact absurd hq1 (hdisj q hqm)
    | @step d ym0 ym hext hd hymd ih =>
      intro hsub hmeet
      have hsub0 : ∀ q ∈ ym0.disk, q ∈ r.toRegion ∨ q ∈ m.disk := fun q hq =>
        hsub q ((hymd q).mpr (mem_extDisk.mpr (Or.inr hq)))
      by_cases hmeet0 : ∃ q ∈ m1.disk, q ∈ ym0.disk
      · exact ih hsub0 hmeet0
      · push_neg at hmeet0
        have hborder := (ym0.mem_ring _).mp hd
        refine ⟨ym0, hext.subset, fun q hq => ⟨hsub0 q hq, fun hq1 => hmeet0 q hq1 hq⟩,
          gedge d, hd, ?_⟩
        rw [gedge2]
        refine (m1.mem_ring d).mpr ⟨?_, fun hc => hmeet0 _ hc hborder.1⟩
        obtain ⟨q, hq1, hqy⟩ := hmeet
        rw [hymd q, mem_extDisk] at hqy
        rcases hqy with rfl | hqy
        · exact hq1
        · exact absurd hq1 fun hc => hmeet0 q hc hqy
  exact key xm hxm hxsub ⟨p, hp1, hxp⟩

/-! ### The corner metric

`mcorner m q` measures how far the matte is from covering the whole
neighbourhood of the grid point `q`: the pixel diagonally opposite `q` counts
once and the two side pixels count twice each.  It vanishes exactly when all
four pixels incident to `q` lie in the matte.
-/

/-- The number of pixels incident to the grid point `q`, other than `q` itself,
that are missing from the matte, the two side pixels counted twice. -/
def mcorner (m : Matte) (q : GPoint) : ℕ :=
  (if q - ccw (ccw 0) ∈ m.disk then 0 else 1)
    + 2 * ((if q - ccw 0 ∈ m.disk then 0 else 1)
      + (if q - ccw (ccw (ccw 0)) ∈ m.disk then 0 else 1))

theorem mcorner_eq_zero_iff {m : Matte} {q : GPoint} :
    mcorner m q = 0 ↔ q - ccw 0 ∈ m.disk ∧ q - ccw (ccw 0) ∈ m.disk
      ∧ q - ccw (ccw (ccw 0)) ∈ m.disk := by
  rw [mcorner]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> by_contra hc <;> simp [hc] at h
  · rintro ⟨h1, h2, h3⟩
    simp [h1, h2, h3]

/-- When the corner metric vanishes at a pixel of the matte, all four pixels
incident to the grid point `q` lie in the matte. -/
theorem mem_disk_of_mem_ltouch {m : Matte} {q : GPoint} (hq : q ∈ m.disk)
    (h : mcorner m q = 0) {p : GPoint} (hp : p ∈ (ltouch q).toRegion) : p ∈ m.disk := by
  obtain ⟨h1, h2, h3⟩ := mcorner_eq_zero_iff.mp h
  have e1 : q - ccw 0 = (q.1 - 1, q.2) := by simp [ccw, Prod.ext_iff]
  have e2 : q - ccw (ccw 0) = (q.1 - 1, q.2 - 1) := by simp [ccw, Prod.ext_iff]
  have e3 : q - ccw (ccw (ccw 0)) = (q.1, q.2 - 1) := by simp [ccw, Prod.ext_iff]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hq' : ((q.1, q.2) : GPoint) ∈ m.disk := hq
  simp only [ltouch, GRect.mem_toRegion] at hp
  have hp4 : p = (q.1 - 1, q.2 - 1) ∨ p = (q.1 - 1, q.2) ∨ p = (q.1, q.2 - 1)
      ∨ p = (q.1, q.2) := by
    simp only [Prod.ext_iff]
    omega
  rcases hp4 with rfl | rfl | rfl | rfl
  · exact h2
  · exact h1
  · exact h3
  · exact hq'

/-- `mcorner` with the three corner offsets written out. -/
theorem mcorner_eq (m : Matte) (q : GPoint) :
    mcorner m q = (if q - ((1 : ℤ), (1 : ℤ)) ∈ m.disk then 0 else 1)
      + 2 * ((if q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk then 0 else 1)
        + (if q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk then 0 else 1)) := by
  have h1 : ccw (0 : GPoint) = ((1 : ℤ), (0 : ℤ)) := by simp [ccw]
  have h2 : ccw ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by simp [ccw]
  have h3 : ccw ((1 : ℤ), (1 : ℤ)) = ((0 : ℤ), (1 : ℤ)) := by simp [ccw]
  rw [mcorner, h1, h2, h3]

/-- Refining the grid lets a matte be extended, inside `r`, so that the corner
metric at a dart of a pixel strictly decreases. -/
theorem refine_mcorner {m : Matte} {r : GRect} {q : GPoint}
    (hq : halfg q ∈ m.disk) (hr : halfg q ∈ r.inset.toRegion)
    (hpos : 0 < mcorner m (halfg q)) :
    ∃ xm : Matte, (∀ z, halfg z ∈ m.disk → z ∈ xm.disk) ∧
      (∀ z ∈ xm.disk, halfg z ∈ r.toRegion ∨ halfg z ∈ m.disk) ∧
      mcorner xm q < mcorner m (halfg q) := by
  -- Extend the refinement of `m` inside the refinement of `r` so as to reach
  -- the subpixel `q - c`; every subpixel of a pixel of `m` comes along.
  have ext_along : ∀ c : GPoint, IsOddg c →
      ∃ xm : Matte, (∀ z, halfg z ∈ m.disk → z ∈ xm.disk) ∧
        (∀ z ∈ xm.disk, halfg z ∈ r.toRegion ∨ halfg z ∈ m.disk) ∧
        q - c ∈ xm.disk ∧ ∀ e : GPoint, halfg (q - e) ∈ m.disk → q - e ∈ xm.disk := by
    intro c hc
    have hcoarse : CoarseIn (refineRect r).toRegion (refineMatte m) :=
      refineMatte_coarseIn m _
    have hmr : ∃ w ∈ (refineMatte m).disk, w ∈ (refineRect r).toRegion :=
      ⟨q, mem_refineMatte.mpr hq, (mem_refineRect r q).mpr (GRect.mem_of_mem_inset hr)⟩
    have hgt : q - c ∈ (gtouch q).toRegion := by
      obtain ⟨s, t⟩ := c
      rcases hc with ⟨h1 | h1, h2 | h2⟩ <;> subst h1 <;> subst h2 <;>
        simp [gtouch] <;> omega
    have hins : q - c ∈ (refineRect r).inset.toRegion := by
      have h0 : q ∈ (refineRect r.inset).toRegion := (mem_refineRect r.inset q).mpr hr
      rw [refine_inset] at h0
      exact (GRect.mem_inset_iff _ q).mp h0 hgt
    obtain ⟨xm, hxm, hxsub, hxc⟩ := coarse_extends_in hcoarse hmr hins
    refine ⟨xm, fun z hz => hxm.subset z (mem_refineMatte.mpr hz), fun z hz => ?_, hxc,
      fun e he => hxm.subset _ (mem_refineMatte.mpr he)⟩
    rcases hxsub z hz with h | h
    · exact Or.inl ((mem_refineRect r z).mp h)
    · exact Or.inr (mem_refineMatte.mp h)
  have mono : ∀ {X Y : Prop} [Decidable X] [Decidable Y], (Y → X) →
      (if X then (0 : ℕ) else 1) ≤ (if Y then 0 else 1) := by
    intro X Y _ _ h
    by_cases hY : Y
    · simp [hY, h hY]
    · by_cases hX : X <;> simp [hX, hY]
  have one : ∀ {X : Prop} [Decidable X], (if X then (0 : ℕ) else 1) ≤ 1 := by
    intro X _
    by_cases hX : X <;> simp [hX]
  have zero : ∀ {X : Prop} [Decidable X], X → (if X then (0 : ℕ) else 1) = 0 := by
    intro X _ hX
    simp [hX]
  rw [mcorner_eq] at hpos
  have hpx := Int.emod_two_eq_zero_or_one q.1
  have hpy := Int.emod_two_eq_zero_or_one q.2
  rcases hpx with hpx | hpx <;> rcases hpy with hpy | hpy
  · -- `q` is the lower-left subpixel: the three corners are the coarse ones.
    have k11 : halfg (q - ((1 : ℤ), (1 : ℤ))) = halfg q - ((1 : ℤ), (1 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k10 : halfg (q - ((1 : ℤ), (0 : ℤ))) = halfg q - ((1 : ℤ), (0 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k01 : halfg (q - ((0 : ℤ), (1 : ℤ))) = halfg q - ((0 : ℤ), (1 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    by_cases hA : halfg q - ((1 : ℤ), (1 : ℤ)) ∈ m.disk
    · by_cases hB : halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk
      · by_cases hC : halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk
        · simp [hA, hB, hC] at hpos
        · obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along ((0 : ℤ), (1 : ℤ)) ⟨Or.inl rfl, Or.inr rfl⟩
          refine ⟨xm, h1, h2, ?_⟩
          rw [mcorner_eq, mcorner_eq]
          have m1 := mono (X := q - ((1 : ℤ), (1 : ℤ)) ∈ xm.disk)
            (Y := halfg q - ((1 : ℤ), (1 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k11]; exact h)
          have m2 := mono (X := q - ((1 : ℤ), (0 : ℤ)) ∈ xm.disk)
            (Y := halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k10]; exact h)
          have m3 := zero hZ
          have b3 : (if halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk then (0 : ℕ) else 1) = 1 := by
            simp [hC]
          omega
      · obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along ((1 : ℤ), (0 : ℤ)) ⟨Or.inr rfl, Or.inl rfl⟩
        refine ⟨xm, h1, h2, ?_⟩
        rw [mcorner_eq, mcorner_eq]
        have m1 := mono (X := q - ((1 : ℤ), (1 : ℤ)) ∈ xm.disk)
          (Y := halfg q - ((1 : ℤ), (1 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k11]; exact h)
        have m3 := mono (X := q - ((0 : ℤ), (1 : ℤ)) ∈ xm.disk)
          (Y := halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k01]; exact h)
        have m2 := zero hZ
        have b2 : (if halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk then (0 : ℕ) else 1) = 1 := by
          simp [hB]
        omega
    · obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along ((1 : ℤ), (1 : ℤ)) ⟨Or.inr rfl, Or.inr rfl⟩
      refine ⟨xm, h1, h2, ?_⟩
      rw [mcorner_eq, mcorner_eq]
      have m2 := mono (X := q - ((1 : ℤ), (0 : ℤ)) ∈ xm.disk)
        (Y := halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k10]; exact h)
      have m3 := mono (X := q - ((0 : ℤ), (1 : ℤ)) ∈ xm.disk)
        (Y := halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k01]; exact h)
      have m1 := zero hZ
      have b1 : (if halfg q - ((1 : ℤ), (1 : ℤ)) ∈ m.disk then (0 : ℕ) else 1) = 1 := by
        simp [hA]
      omega
  · -- `q` is the upper-left subpixel.
    have k11 : halfg (q - ((1 : ℤ), (1 : ℤ))) = halfg q - ((1 : ℤ), (0 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k10 : halfg (q - ((1 : ℤ), (0 : ℤ))) = halfg q - ((1 : ℤ), (0 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k01 : halfg (q - ((0 : ℤ), (1 : ℤ))) = halfg q := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along ((1 : ℤ), (0 : ℤ)) ⟨Or.inr rfl, Or.inl rfl⟩
    refine ⟨xm, h1, h2, ?_⟩
    rw [mcorner_eq, mcorner_eq]
    have m1 := mono (X := q - ((1 : ℤ), (1 : ℤ)) ∈ xm.disk)
      (Y := halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k11]; exact h)
    have m2 := zero hZ
    have m3 := zero (hE ((0 : ℤ), (1 : ℤ)) (by rw [k01]; exact hq))
    have o2 := one (X := halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk)
    have o3 := one (X := halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk)
    omega
  · -- `q` is the lower-right subpixel.
    have k11 : halfg (q - ((1 : ℤ), (1 : ℤ))) = halfg q - ((0 : ℤ), (1 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k10 : halfg (q - ((1 : ℤ), (0 : ℤ))) = halfg q := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k01 : halfg (q - ((0 : ℤ), (1 : ℤ))) = halfg q - ((0 : ℤ), (1 : ℤ)) := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along ((0 : ℤ), (1 : ℤ)) ⟨Or.inl rfl, Or.inr rfl⟩
    refine ⟨xm, h1, h2, ?_⟩
    rw [mcorner_eq, mcorner_eq]
    have m1 := mono (X := q - ((1 : ℤ), (1 : ℤ)) ∈ xm.disk)
      (Y := halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk) fun h => hE _ (by rw [k11]; exact h)
    have m3 := zero hZ
    have m2 := zero (hE ((1 : ℤ), (0 : ℤ)) (by rw [k10]; exact hq))
    have o2 := one (X := halfg q - ((1 : ℤ), (0 : ℤ)) ∈ m.disk)
    have o3 := one (X := halfg q - ((0 : ℤ), (1 : ℤ)) ∈ m.disk)
    omega
  · -- `q` is the upper-right subpixel: all three corners are the coarse pixel.
    have k11 : halfg (q - ((1 : ℤ), (1 : ℤ))) = halfg q := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k10 : halfg (q - ((1 : ℤ), (0 : ℤ))) = halfg q := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    have k01 : halfg (q - ((0 : ℤ), (1 : ℤ))) = halfg q := by
      simp only [halfg, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
      omega
    obtain ⟨xm, h1, h2, hZ, hE⟩ := ext_along 0 ⟨Or.inl rfl, Or.inl rfl⟩
    refine ⟨xm, h1, h2, ?_⟩
    rw [mcorner_eq, mcorner_eq]
    have m1 := zero (hE ((1 : ℤ), (1 : ℤ)) (by rw [k11]; exact hq))
    have m2 := zero (hE ((1 : ℤ), (0 : ℤ)) (by rw [k10]; exact hq))
    have m3 := zero (hE ((0 : ℤ), (1 : ℤ)) (by rw [k01]; exact hq))
    omega

end FourColor

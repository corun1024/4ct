import FourColor.Kempe
import FourColor.Snip
import FourColor.Sew

/-!
# Cutting a map along a ring and along its reverse

`FourColor/Snip.lean` cuts a planar map along a ring `r`, producing a disk map
and a remainder map.  The construction is asymmetric: the disk carries the
darts of `DiskN r`, the remainder the darts outside `DiskE r`.  Here we cut
again along the *reverse edge-conjugate* `revRing r = (r.map edge).reverse`,
which runs around the outside of `r` through the same faces in reverse order.
The two cuts together give a symmetric cover: the disk of `revRing r` is
exactly the complement of `DiskN r`.

Along the way we single out the rings that are worth cutting along: a *proper*
ring is nonempty and is not a single edge orbit, and a ring is *nontrivial of
order `m`* when more than `m` faces lie strictly inside it and more than `m`
lie strictly outside.  A *chord* of a ring is a dart `x` with both `x` and
`edge x` in the face band of the ring; cutting the ring at a chord splits it
into two smaller rings, the *chord rings* of `x` and of `edge x`.

## Main definitions

* `Hypermap.ProperRing` — a ring that is not empty and not an edge orbit.
* `Hypermap.faceCard` — the number of faces met by a set of darts.
* `Hypermap.NontrivialRing` — more than `m` faces on each side of the ring.
* `Hypermap.revRing` — the reverse edge-conjugate of a ring.
* `arc`, `rotTo` — the arcs of a cyclic list between two of its darts.
* `Hypermap.chordRing` — the ring cut off by a chord.
* `Hypermap.revSnipDisk`, `Hypermap.revSnipRem`, `Hypermap.revSnipdRing`,
  `Hypermap.revSniprRing` — the two maps and border rings of the reverse cut.

## Main results

* `Hypermap.scycle_revRing`, `Hypermap.fband_revRing` — the reverse ring is a
  face-simple ring with the same face band.
* `Hypermap.diskN_revRing` — its disk is the exact complement of `DiskN r`;
  hence `Hypermap.diskF_revRing` and `Hypermap.nontrivial_revRing`.
* `Hypermap.nontrivialRing_properRing` — a nontrivial ring is proper.
* `exists_arc_split` — the two arcs between two darts of a duplicate-free
  cycle concatenate into a rotation of it.
* `Hypermap.scycle_chordRing`, `Hypermap.diskN_chordRing`,
  `Hypermap.fband_chordRing`, `Hypermap.diskF_chordRing` — the two chord rings
  of a chord split the disk and the face band of the ring.
* `Hypermap.nontrivial_chordRing` — a chord ring with a face inside it is a
  strictly shorter nontrivial ring.
* `Hypermap.revSnip_patch`, `Hypermap.planar_revSnipDisk`,
  `Hypermap.planar_revSnipRem` — the reverse cut is a patch of planar maps.
* `Hypermap.ring_disk_chord` — a chord of the border ring of the disk map
  yields a strictly shorter nontrivial ring.
* `Hypermap.cface_snipd_iff` — the disk projection reflects face orbits.
* `Hypermap.rev_ring_cotrace` — the ring traces of the disk of `r` are exactly
  the ring traces of the remainder of `revRing r`.
* `Hypermap.ring_disk_closed` — hence the ring traces of the disk of a ring of
  a cubic map are Kempe-closed.
* `Hypermap.colorable_from_ring` — a ring trace of the disk of `r` together
  with the reversed trace of the disk of `revRing r` colours `G`.
-/

namespace FourColor

/-! ### Arcs of a cyclic list

A chord cuts its ring into two arcs.  `rotTo l x` is the rotation of `l` that
starts at `x`, and `arc l x y` is the piece of that rotation running from `x`
up to, but not including, `y`.  For a duplicate-free `l` the two arcs between
two of its darts concatenate back into a rotation of `l`. -/

section Arc

variable {α : Type*} [DecidableEq α]

/-- The rotation of `l` that starts at `x`. -/
def rotTo (l : List α) (x : α) : List α := l.rotate (l.idxOf x)

/-- The arc of the cycle `l` running from `x` up to, but not including, `y`. -/
def arc (l : List α) (x y : α) : List α := (rotTo l x).take ((rotTo l x).idxOf y)

/-- `rotTo` is a rotation. -/
theorem exists_rotate_eq_rotTo (l : List α) (x : α) : ∃ n, l.rotate n = rotTo l x :=
  ⟨l.idxOf x, rfl⟩

/-- The rotation starting at `x` does start at `x`. -/
theorem exists_rotTo_cons {l : List α} {x : α} (hx : x ∈ l) : ∃ t, rotTo l x = x :: t := by
  have hi : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  refine ⟨l.drop (l.idxOf x + 1) ++ l.take (l.idxOf x), ?_⟩
  rw [rotTo, List.rotate_eq_drop_append_take (le_of_lt hi), List.drop_eq_getElem_cons hi,
    List.getElem_idxOf, List.cons_append]

/-- In a duplicate-free list there is only one rotation starting at a given
dart. -/
theorem rotTo_eq_of_rotate {l : List α} (hl : l.Nodup) {m : ℕ} {x : α} {t : List α}
    (h : l.rotate m = x :: t) : rotTo l x = x :: t := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hklt : m % l.length < l.length := Nat.mod_lt _ hpos
  have hrot : l.rotate (m % l.length) = x :: t := by rw [List.rotate_mod]; exact h
  have hrot' : l[m % l.length] :: (l.drop (m % l.length + 1) ++ l.take (m % l.length))
      = x :: t := by
    rw [← hrot, List.rotate_eq_drop_append_take (le_of_lt hklt),
      List.drop_eq_getElem_cons hklt, List.cons_append]
  have hxk : l[m % l.length] = x := by injection hrot'
  have hxl : x ∈ l := hxk ▸ List.getElem_mem hklt
  have hidx : l.idxOf x = m % l.length := by
    refine (hl.getElem_inj_iff (hi := List.idxOf_lt_length_iff.mpr hxl) (hj := hklt)).mp ?_
    rw [List.getElem_idxOf, hxk]
  rw [rotTo, hidx, hrot]

/-- Reading an arc off a splitting of the rotation. -/
theorem arc_eq_of_rotTo {l : List α} {x y : α} {p q : List α}
    (h : rotTo l x = (x :: p) ++ (y :: q)) (hy : y ∉ x :: p) : arc l x y = x :: p := by
  rw [arc, h, List.idxOf_append_of_notMem hy, List.idxOf_cons_self, Nat.add_zero,
    List.take_left]

/-- **The two arcs between two darts of a duplicate-free cycle concatenate into
a rotation of it.** -/
theorem exists_arc_split {l : List α} (hl : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : x ≠ y) : ∃ p q : List α, arc l x y = x :: p ∧ arc l y x = y :: q ∧
      ∃ n, l.rotate n = (x :: p) ++ (y :: q) := by
  obtain ⟨t, ht⟩ := exists_rotTo_cons hx
  have hyt : y ∈ t := by
    have hy' : y ∈ rotTo l x := by rw [rotTo, List.mem_rotate]; exact hy
    rw [ht] at hy'
    exact (List.mem_cons.mp hy').resolve_left (Ne.symm hxy)
  obtain ⟨p, q, hpq⟩ := List.append_of_mem hyt
  have hsplit : rotTo l x = (x :: p) ++ (y :: q) := by rw [ht, hpq]; rfl
  have hnodup : ((x :: p) ++ (y :: q)).Nodup := by
    rw [← hsplit, rotTo]
    exact List.nodup_rotate.mpr hl
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnodup
  have hyp : y ∉ x :: p := fun hc => hdisj y hc y List.mem_cons_self rfl
  have hxq : x ∉ y :: q := fun hc => hdisj x List.mem_cons_self x hc rfl
  have hrot2 : rotTo l y = y :: (q ++ (x :: p)) := by
    refine rotTo_eq_of_rotate hl (m := l.idxOf x + (x :: p).length) ?_
    rw [← List.rotate_rotate, ← rotTo, hsplit, List.rotate_append_length_eq, List.cons_append]
  exact ⟨p, q, arc_eq_of_rotTo hsplit hyp,
    arc_eq_of_rotTo (by rw [hrot2, List.cons_append]) hxq, l.idxOf x, hsplit⟩

/-- The darts of an arc are darts of the list. -/
theorem mem_of_mem_arc {l : List α} {x y z : α} (h : z ∈ arc l x y) : z ∈ l := by
  have h1 := List.mem_of_mem_take h
  rwa [rotTo, List.mem_rotate] at h1

end Arc

/-! ### Cyclic successors -/

section CyclicNextAux

variable {α β : Type*}

/-- Two equal indices select the same dart. -/
private theorem getElem_congr_idx {l : List α} {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i] = l[j] := by subst h; rfl

/-- The dart at the next cyclic position is the cyclic successor. -/
theorem cyclicNext_getElem {l : List α} {i k : ℕ} (hi : i < l.length) (hk : k < l.length)
    (hik : k = (i + 1) % l.length) : CyclicNext l l[i] l[k] := by
  have hrot : l.rotate i = l[i] :: (l.drop (i + 1) ++ l.take i) := by
    rw [List.rotate_eq_drop_append_take (le_of_lt hi), List.drop_eq_getElem_cons hi,
      List.cons_append]
  refine ⟨i, l.drop (i + 1) ++ l.take i, hrot, ?_⟩
  have key : ∀ u : List α, l.rotate i = l[i] :: u → l[k] = u.headD l[i] := by
    intro u hu
    match u with
    | [] =>
      have hlen : l.length = 1 := by
        have h1 := congrArg List.length hu
        rw [List.length_rotate] at h1
        simpa using h1
      rw [List.headD_nil]
      exact getElem_congr_idx (by omega) hk hi
    | a :: t =>
      have hlen1 : 1 < l.length := by
        have h1 := congrArg List.length hu
        rw [List.length_rotate] at h1
        simp only [List.length_cons] at h1
        omega
      have h2 := List.getElem_of_eq hu (show 1 < (l.rotate i).length by
        rw [List.length_rotate]; omega)
      rw [List.getElem_rotate, Nat.add_comm 1 i] at h2
      rw [List.headD_cons]
      exact (getElem_congr_idx hik hk (Nat.mod_lt _ (by omega))).trans h2
  exact key _ hrot

/-- The head of a mapped list. -/
theorem headD_map (f : β → α) (l : List β) (d : β) :
    (l.map f).headD (f d) = f (l.headD d) := by
  match l with
  | [] => rfl
  | _ :: _ => rfl

/-- Cyclic successors are reflected by an injective map. -/
theorem cyclicNext_of_map {l : List β} {f : β → α} (hf : Function.Injective f) {u v : β}
    (h : CyclicNext (l.map f) (f u) (f v)) : CyclicNext l u v := by
  obtain ⟨n, t, ht, hv⟩ := h
  rw [← List.map_rotate] at ht
  obtain ⟨u', s, hls, hfu, hts⟩ := List.map_eq_cons_iff.mp ht
  refine ⟨n, s, by rw [hls, hf hfu], ?_⟩
  rw [← hts, headD_map] at hv
  exact hf hv

end CyclicNextAux

namespace Hypermap

open Equiv Equiv.Perm

variable {D : Type*}

/-! ### Proper rings

A ring is proper when it is nonempty and is not just an edge orbit; only such
rings delimit a disk that is worth cutting out. -/

section ProperRing

variable (G : Hypermap D)

/-- A proper ring: a nonempty ring that is not a two-dart edge orbit. -/
def ProperRing : List D → Prop
  | [] => False
  | [_] => False
  | [x, y] => G.edge x ≠ y
  | _ :: _ :: _ :: _ => True

@[simp] theorem properRing_nil : ¬ G.ProperRing ([] : List D) := id

@[simp] theorem properRing_singleton (x : D) : ¬ G.ProperRing [x] := id

@[simp] theorem properRing_pair (x y : D) : G.ProperRing [x, y] ↔ G.edge x ≠ y := Iff.rfl

@[simp] theorem properRing_cons_cons_cons (x y z : D) (p : List D) :
    G.ProperRing (x :: y :: z :: p) := trivial

/-- Any ring with more than two darts is proper. -/
theorem properRing_of_two_lt_length {r : List D} (h : 2 < r.length) : G.ProperRing r := by
  match r with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | _ :: _ :: _ :: _ => trivial

variable {G}

/-- Being a proper ring is invariant under rotation. -/
theorem properRing_rotate (hplain : G.Plain) {r : List D} {n : ℕ} :
    G.ProperRing (r.rotate n) ↔ G.ProperRing r := by
  rcases Nat.lt_or_ge 2 r.length with hlt | hle
  · have h1 : 2 < (r.rotate n).length := by rwa [List.length_rotate]
    simp only [G.properRing_of_two_lt_length hlt, G.properRing_of_two_lt_length h1]
  match r with
  | [] => simp
  | [x] =>
    rw [show [x].rotate n = [x] by rw [← List.rotate_mod]; simp]
  | [x, y] =>
    rw [← List.rotate_mod, show ([x, y] : List D).length = 2 from rfl]
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h2 | h2 <;> rw [h2]
    · simp
    · rw [show ([x, y] : List D).rotate 1 = [y, x] from rfl, properRing_pair, properRing_pair]
      exact ⟨fun h he => h (by rw [← he]; exact hplain.edge_edge x),
        fun h he => h (by rw [← he]; exact hplain.edge_edge y)⟩
  | _ :: _ :: _ :: _ => simp at hle

end ProperRing

/-! ### Counting faces

`faceCard A` counts the faces that meet `A`; this is the reference's
`fcard face A` when `A` is closed under `face`. -/

section FaceCard

variable (G : Hypermap D)

open scoped Classical in
/-- The number of faces met by a set of darts. -/
noncomputable def faceCard (A : D → Prop) : ℕ :=
  (Quotient.mk (SameCycle.setoid G.face) '' {x | A x}).ncard

variable {G}

/-- A set meets a face exactly when it is nonempty. -/
theorem zero_lt_faceCard [Finite D] {A : D → Prop} : 0 < G.faceCard A ↔ ∃ x, A x := by
  classical
  rw [faceCard, Set.ncard_pos (Set.toFinite _)]
  constructor
  · rintro ⟨-, x, hx, -⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨_, x, hx, rfl⟩

/-- A set meets more than one face exactly when it contains two darts in
distinct faces. -/
theorem one_lt_faceCard [Finite D] {A : D → Prop} :
    1 < G.faceCard A ↔ ∃ x y, A x ∧ A y ∧ ¬ G.CFace x y := by
  classical
  rw [faceCard, Set.one_lt_ncard (Set.toFinite _)]
  constructor
  · rintro ⟨-, ⟨x, hx, rfl⟩, -, ⟨y, hy, rfl⟩, hne⟩
    exact ⟨x, y, hx, hy, fun hc => hne (Quotient.sound hc)⟩
  · rintro ⟨x, y, hx, hy, hne⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, fun hc => hne (Quotient.exact hc)⟩

/-- The face count only depends on the set of darts. -/
theorem faceCard_congr {A B : D → Prop} (h : ∀ x, A x ↔ B x) : G.faceCard A = G.faceCard B :=
  congrArg G.faceCard (funext fun x => propext (h x))

/-- An empty set of darts meets no face. -/
theorem faceCard_eq_zero [Finite D] {A : D → Prop} (h : ∀ x, ¬ A x) : G.faceCard A = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := zero_lt_faceCard.mp (Nat.pos_of_ne_zero hne)
  exact h x hx

end FaceCard

/-! ### Nontrivial rings -/

section NontrivialRing

variable (G : Hypermap D)

/-- `r` is nontrivial of order `m` when more than `m` faces lie strictly inside
it and more than `m` lie strictly outside. -/
def NontrivialRing (m : ℕ) (r : List D) : Prop :=
  m < G.faceCard (G.DiskF r) ∧ m < G.faceCard (G.DiskFC r)

variable {G}

/-- A ring is nontrivial of order zero when there is a face on each side. -/
theorem nontrivialRing_zero_iff [Finite D] {r : List D} :
    G.NontrivialRing 0 r ↔ (∃ x, G.DiskF r x) ∧ ∃ x, G.DiskFC r x := by
  rw [NontrivialRing, zero_lt_faceCard, zero_lt_faceCard]

/-- A ring is nontrivial of order one when there are two distinct faces on each
side. -/
theorem nontrivialRing_one_iff [Finite D] {r : List D} :
    G.NontrivialRing 1 r ↔
      (∃ x y, G.DiskF r x ∧ G.DiskF r y ∧ ¬ G.CFace x y) ∧
        ∃ x y, G.DiskFC r x ∧ G.DiskFC r y ∧ ¬ G.CFace x y := by
  rw [NontrivialRing, one_lt_faceCard, one_lt_faceCard]

end NontrivialRing

/-! ### The reverse ring -/

section RevRing

variable (G : Hypermap D)

/-- The reverse edge-conjugate of a ring: it runs around the outside of `r`
through the same faces, in reverse order. -/
def revRing (r : List D) : List D := (r.map G.edge).reverse

variable {G}

@[simp] theorem length_revRing (r : List D) : (G.revRing r).length = r.length := by
  simp [revRing]

/-- The reverse ring of the reverse ring is the ring itself. -/
theorem revRing_revRing (hplain : G.Plain) (r : List D) : G.revRing (G.revRing r) = r := by
  simp only [revRing, List.map_reverse, List.reverse_reverse, List.map_map]
  simp [Function.comp_def, hplain.edge_edge]

/-- A dart lies on the reverse ring exactly when its edge lies on the ring. -/
theorem mem_revRing (hplain : G.Plain) {r : List D} {x : D} :
    x ∈ G.revRing r ↔ G.edge x ∈ r := by
  rw [revRing, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [hplain.edge_edge]
  · intro h; exact ⟨G.edge x, h, hplain.edge_edge x⟩

/-- The reverse ring is proper exactly when the ring is. -/
theorem properRing_revRing (hplain : G.Plain) {r : List D} :
    G.ProperRing (G.revRing r) ↔ G.ProperRing r := by
  rcases Nat.lt_or_ge 2 r.length with hlt | hle
  · have h1 : 2 < (G.revRing r).length := by rwa [length_revRing]
    simp only [G.properRing_of_two_lt_length hlt, G.properRing_of_two_lt_length h1]
  match r with
  | [] => simp [revRing]
  | [x] => simp [revRing]
  | [x, y] =>
    rw [show G.revRing [x, y] = [G.edge y, G.edge x] from rfl, properRing_pair, properRing_pair,
      hplain.edge_edge]
    exact ne_comm
  | _ :: _ :: _ :: _ => simp at hle

end RevRing

/-! ### Positions in a cyclic chain

Both the reverse ring and the chord rings are described by their positions, so
the cyclic chain condition is read off the indices. -/

section CyclicPositions

variable {α : Type*} {e : α → α → Prop} {l : List α}

/-- In a cyclic chain each dart is linked to the dart at the next cyclic
position. -/
theorem rel_getElem_succ (hcyc : IsCyclicChain e l) {i k : ℕ} (hi : i < l.length)
    (hk : k < l.length) (hik : k = (i + 1) % l.length) : e l[i] l[k] := by
  rcases Nat.lt_or_ge (i + 1) l.length with hlt | hge
  · have hki : k = i + 1 := by rw [hik, Nat.mod_eq_of_lt hlt]
    subst hki
    exact List.isChain_iff_getElem.mp hcyc.isChain i hlt
  · have hi1 : i + 1 = l.length := by omega
    have hk0 : k = 0 := by rw [hik, hi1, Nat.mod_self]
    subst hk0
    refine hcyc.2 _ ?_ _ ?_
    · rw [Option.mem_def, List.getLast?_eq_getElem?, show l.length - 1 = i by omega,
        List.getElem?_eq_getElem hi]
    · rw [Option.mem_def, List.head?_eq_getElem?, List.getElem?_eq_getElem hk]

/-- A list is a cyclic chain as soon as each dart is linked to the dart at the
next cyclic position. -/
theorem isCyclicChain_of_rel_getElem
    (h : ∀ i k, ∀ hi : i < l.length, ∀ hk : k < l.length,
      k = (i + 1) % l.length → e l[i] l[k]) : IsCyclicChain e l := by
  refine ⟨List.isChain_iff_getElem.mpr fun i hi =>
    h i (i + 1) (by omega) hi (by rw [Nat.mod_eq_of_lt hi]), fun a ha b hb => ?_⟩
  have hne : l ≠ [] := by rintro rfl; simp at hb
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hae : a = l[l.length - 1] := by
    rw [Option.mem_def, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)] at ha
    exact (Option.some_inj.mp ha).symm
  have hbe : b = l[0] := by
    rw [Option.mem_def, List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at hb
    exact (Option.some_inj.mp hb).symm
  subst hae
  subst hbe
  exact h (l.length - 1) 0 (by omega) hpos (by rw [Nat.sub_add_cancel hpos, Nat.mod_self])

/-- In a duplicate-free cyclic chain each dart is linked to its cyclic
successor. -/
theorem rel_next [DecidableEq α] (hcyc : IsCyclicChain e l) (hl : l.Nodup) {x : α}
    (hx : x ∈ l) : e x (l.next x hx) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.next_getElem l hl i hi]
  exact rel_getElem_succ hcyc hi _ rfl

/-- In a duplicate-free cyclic chain each dart is linked to from its cyclic
predecessor. -/
theorem rel_prev [DecidableEq α] (hcyc : IsCyclicChain e l) (hl : l.Nodup) {x : α}
    (hx : x ∈ l) : e (l.prev x hx) x := by
  have h1 := rel_next hcyc hl (List.prev_mem l x hx)
  rwa [List.next_prev l hl x hx] at h1

/-- The last dart of a list with a head, without its nonemptiness proof. -/
theorem getLast_cons_eq_getLastD (x : α) (p : List α) :
    (x :: p).getLast (List.cons_ne_nil x p) = p.getLastD x := by
  have h2 := getLast?_cons_eq_some x p
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p)] at h2
  exact Option.some_inj.mp h2

/-- The endpoint of a chain, as a `getLastD`. -/
theorem getLastD_of_getLast (x : α) (p : List α) {y : α}
    (h : (x :: p).getLast (List.cons_ne_nil x p) = y) : p.getLastD x = y := by
  rw [← getLast_cons_eq_getLastD x p, h]

end CyclicPositions

/-! ### The reverse ring is a ring -/

section RevRingCycle

variable {G : Hypermap D} {r : List D}

/-- A dart of the reverse ring, read off the ring backwards. -/
theorem getElem_revRing {i j : ℕ} (hi : i < (G.revRing r).length) (hj : j < r.length)
    (hij : j = r.length - 1 - i) : (G.revRing r)[i] = G.edge r[j] := by
  subst hij
  simp [revRing]

/-- The reverse ring is again an R-cycle. -/
theorem isCyclicChain_revRing (hplain : G.Plain) (hcyc : IsCyclicChain G.Rlink r) :
    IsCyclicChain G.Rlink (G.revRing r) := by
  refine isCyclicChain_of_rel_getElem fun i k hi hk hik => ?_
  rw [length_revRing] at hi hk hik
  -- the cyclic successor of `r.length - 1 - k` is `r.length - 1 - i`
  have hstep : (r.length - 1 - k + 1) % r.length = r.length - 1 - i := by
    rcases Nat.lt_or_ge (i + 1) r.length with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hik
      rw [Nat.mod_eq_of_lt (by omega), hik]
      omega
    · have hi1 : i + 1 = r.length := by omega
      rw [hi1, Nat.mod_self] at hik
      subst hik
      rw [show r.length - 1 - 0 + 1 = r.length by omega, Nat.mod_self]
      omega
  have hlink := rel_getElem_succ hcyc (i := r.length - 1 - k) (k := r.length - 1 - i)
    (by omega) (by omega) hstep.symm
  have h2 : G.CFace (G.edge r[r.length - 1 - k]) r[r.length - 1 - i] := hlink
  change G.CFace (G.edge (G.revRing r)[i]) (G.revRing r)[k]
  rw [getElem_revRing _ (show r.length - 1 - i < r.length by omega) rfl,
    getElem_revRing _ (show r.length - 1 - k < r.length by omega) rfl, hplain.edge_edge]
  exact h2.symm

/-- The reverse ring is face-simple. -/
theorem simple_revRing (hcyc : IsCyclicChain G.Rlink r) (hsim : G.Simple r) :
    G.Simple (G.revRing r) := by
  classical
  set Q := Quotient.mk (SameCycle.setoid G.face) with hQ
  have hmap : (r.map G.edge).map Q = (r.map Q).rotate 1 := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_map] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_rotate, List.getElem_map]
    simp only [List.length_map]
    exact Quotient.sound (rel_getElem_succ hcyc h1 _ rfl)
  rw [simple_iff_nodup_map] at hsim ⊢
  rw [revRing, List.map_reverse, hmap, List.nodup_reverse, List.nodup_rotate]
  exact hsim

/-- The reverse ring is a face-simple R-cycle. -/
theorem scycle_revRing (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r) :
    G.Scycle G.Rlink (G.revRing r) :=
  ⟨isCyclicChain_revRing hplain hscyc.isCyclicChain,
    simple_revRing hscyc.isCyclicChain hscyc.simple⟩

/-- The reverse ring has the same face band as the ring. -/
theorem fband_revRing (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r) {x : D} :
    G.Fband (G.revRing r) x ↔ G.Fband r x := by
  classical
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [mem_revRing hplain] at hy
    refine ⟨r.next (G.edge y) hy, List.next_mem _ _ _, ?_⟩
    have h1 : G.CFace (G.edge (G.edge y)) (r.next (G.edge y) hy) :=
      rel_next hscyc.isCyclicChain hscyc.nodup hy
    rw [hplain.edge_edge] at h1
    exact hxy.trans h1
  · rintro ⟨y, hy, hxy⟩
    refine ⟨G.edge (r.prev y hy), ?_, ?_⟩
    · rw [mem_revRing hplain, hplain.edge_edge]
      exact List.prev_mem _ _ _
    · have h1 : G.CFace (G.edge (r.prev y hy)) y :=
        rel_prev hscyc.isCyclicChain hscyc.nodup hy
      exact hxy.trans h1.symm

end RevRingCycle

/-! ### The disk of the reverse ring

The disk delimited by `revRing r` is the exact complement of the disk
delimited by `r`.  The proof runs along a contour path from a dart of the ring
to an arbitrary dart, and is where the reverse ring earns its name. -/

section RevRingDisk

variable [Finite D] {G : Hypermap D} {r : List D}

/-- Only the modulus two admits a position whose cyclic successor's cyclic
successor is itself. -/
private theorem length_le_two_of_next_next {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hj' : j = (i + 1) % n) (hi' : i = (j + 1) % n) : n ≤ 2 := by
  by_contra hcon0
  have hcon : 2 < n := by omega
  rcases Nat.lt_or_ge (i + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hj'
    subst hj'
    rcases Nat.lt_or_ge (i + 1 + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hi'; omega
    · rw [show i + 1 + 1 = n by omega, Nat.mod_self] at hi'; omega
  · rw [show i + 1 = n by omega, Nat.mod_self] at hj'
    subst hj'
    rw [Nat.mod_eq_of_lt (by omega)] at hi'
    omega

/-- The edge of a dart of a proper ring lies outside the disk of that ring. -/
theorem diskN_edge_ring (hplan : G.Planar) (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r)
    (hproper : G.ProperRing r) {x : D} (hx : x ∈ r) : ¬ G.DiskN r (G.edge x) := by
  -- first: the edge of a ring dart is itself off the ring
  have hex : G.edge x ∉ r := by
    intro hexr
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hexr
    have hmodi : (i + 1) % r.length < r.length := Nat.mod_lt _ (by omega)
    have hmodj : (j + 1) % r.length < r.length := Nat.mod_lt _ (by omega)
    -- `edge x` and `x` follow each other around the ring
    have hstep1 : G.edge x = r[(i + 1) % r.length] := by
      refine hscyc.simple.eq_of_cface hexr (List.getElem_mem hmodi) ?_
      have h1 : G.CFace (G.edge r[i]) r[(i + 1) % r.length] :=
        rel_getElem_succ hscyc.isCyclicChain hi hmodi rfl
      rwa [hxi] at h1
    have hstep2 : x = r[(j + 1) % r.length] := by
      refine hscyc.simple.eq_of_cface hx (List.getElem_mem hmodj) ?_
      have h1 : G.CFace (G.edge r[j]) r[(j + 1) % r.length] :=
        rel_getElem_succ hscyc.isCyclicChain hj hmodj rfl
      rwa [hxj, hplain.edge_edge] at h1
    have hj' : j = (i + 1) % r.length :=
      (hscyc.nodup.getElem_inj_iff (hi := hj) (hj := hmodi)).mp (by rw [hxj, hstep1])
    have hi' : i = (j + 1) % r.length :=
      (hscyc.nodup.getElem_inj_iff (hi := hi) (hj := hmodj)).mp (by rw [hxi, hstep2])
    have hle := length_le_two_of_next_next hi hj hj' hi'
    rcases Nat.lt_or_ge r.length 2 with hlt2 | hge2
    · -- a one-dart ring: `x` would be its own edge
      have hij : (r[i] : D) = r[j] :=
        (hscyc.nodup.getElem_inj_iff (hi := hi) (hj := hj)).mpr (by omega)
      exact hplain.edge_ne x (hxi.symm.trans (hij.trans hxj)).symm
    · -- a two-dart ring: it would be an edge orbit, contradicting properness
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by omega : r.length = 2)
      subst hab
      rw [properRing_pair] at hproper
      simp only [List.length_cons, List.length_nil] at hi hj hj'
      have h01 : i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by omega
      rcases h01 with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
      · subst hi0; subst hj1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hxi hxj
        exact hproper (by rw [hxi, hxj])
      · subst hi1; subst hj0
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hxi hxj
        exact hproper (by rw [hxj, hplain.edge_edge]; exact hxi.symm)
  intro hcon
  rcases diskN_iff.mp hcon with h | h
  · exact hex h
  · exact ((diskE_edge_iff hplan hscyc).mp h).2 hx

/-- The step of the induction proving `diskN_revRing`. -/
private theorem diskN_revRing_aux (hplan : G.Planar) (hplain : G.Plain)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) :
    ∀ (p : List D) (x : D), List.IsChain G.Clink (x :: p) → G.edge (p.getLastD x) ∈ r →
      (G.DiskN (G.revRing r) x ↔ ¬ G.DiskN r x) := by
  have hscycr : G.Scycle G.Rlink (G.revRing r) := scycle_revRing hplain hscyc
  -- a dart whose edge lies on the ring is in the reverse disk and not in the disk
  have hmem : ∀ z : D, G.edge z ∈ r → (G.DiskN (G.revRing r) z ↔ ¬ G.DiskN r z) := by
    intro z hz
    refine iff_of_true (diskN_of_mem ((mem_revRing hplain).mpr hz)) ?_
    have h1 := diskN_edge_ring hplan hplain hscyc hproper hz
    rwa [hplain.edge_edge] at h1
  intro p
  induction p with
  | nil => intro x _ hlast; exact hmem x hlast
  | cons y p ih =>
    intro x hchain hlast
    obtain ⟨hxy, htail⟩ := List.isChain_cons_cons.mp hchain
    rw [getLastD_cons] at hlast
    rcases hxy with hxy | hxy
    · subst hxy
      rw [diskN_node_iff, diskN_node_iff]
      exact ih y htail hlast
    · subst hxy
      by_cases hex : G.edge x ∈ r
      · exact hmem x hex
      have hxrr : x ∉ G.revRing r := fun hc => hex ((mem_revRing hplain).mp hc)
      by_cases hxr : x ∈ r
      · -- the ring dart `x` is outside the reverse disk
        refine iff_of_false (fun hc => ?_) (fun hc => hc (diskN_of_mem hxr))
        have h1 : G.DiskE (G.revRing r) (G.edge x) :=
          diskE_edge hplan hscycr ⟨hc, hxrr⟩
        exact h1.2 ((mem_revRing hplain).mpr (by rwa [hplain.edge_edge]))
      · have hexrr : G.edge x ∉ G.revRing r := fun hc =>
          hxr (by rw [← hplain.edge_edge x]; exact (mem_revRing hplain).mp hc)
        have hl : G.DiskN (G.revRing r) x ↔ G.DiskN (G.revRing r) (G.edge x) := by
          constructor
          · intro hc
            exact (diskE_edge hplan hscycr ⟨hc, hxrr⟩).1
          · intro hc
            exact ((diskE_edge_iff hplan hscycr).mp ⟨hc, hexrr⟩).1
        have hrgt : G.DiskN r x ↔ G.DiskN r (G.edge x) := by
          constructor
          · intro hc
            exact (diskE_edge hplan hscyc ⟨hc, hxr⟩).1
          · intro hc
            exact ((diskE_edge_iff hplan hscyc).mp ⟨hc, hex⟩).1
        rw [hl, hrgt, show G.edge x = G.node (G.face x) from (hplain.node_face x).symm,
          diskN_node_iff, diskN_node_iff]
        exact ih (G.face x) htail hlast

/-- **The disk of the reverse ring is the complement of the disk**. -/
theorem diskN_revRing (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D} :
    G.DiskN (G.revRing r) x ↔ ¬ G.DiskN r x := by
  obtain ⟨y, hy⟩ : ∃ y, y ∈ r := by
    rcases r with _ | ⟨a, t⟩
    · exact absurd hproper (by simp)
    · exact ⟨a, List.mem_cons_self⟩
  obtain ⟨p, hchain, hlast⟩ := G.connected_clink_list hconn x (G.edge y)
  refine diskN_revRing_aux hplan hplain hscyc hproper p x hchain ?_
  rw [getLastD_of_getLast x p hlast, hplain.edge_edge]
  exact hy

/-- The face-closed disk of the reverse ring is the outside of the ring. -/
theorem diskF_revRing (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D} :
    G.DiskF (G.revRing r) x ↔ G.DiskFC r x := by
  rw [DiskF, DiskFC, diskN_revRing hplan hplain hconn hscyc hproper,
    fband_revRing hplain hscyc]

/-- The outside of the reverse ring is the face-closed disk of the ring. -/
theorem diskFC_revRing (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D} :
    G.DiskFC (G.revRing r) x ↔ G.DiskF r x := by
  rw [DiskF, DiskFC, diskN_revRing hplan hplain hconn hscyc hproper,
    fband_revRing hplain hscyc, not_not]

end RevRingDisk

/-! ### Nontrivial rings are proper

A ring with a face on each side cannot be empty, a loop, or an edge orbit: an
edge orbit has nothing outside it at all. -/

section NontrivialProper

variable [Finite D] {G : Hypermap D} {r : List D}

/-- A nontrivial ring is a proper ring. -/
theorem nontrivialRing_properRing (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) {m : ℕ}
    (hnt : G.NontrivialRing m r) : G.ProperRing r := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · -- the empty ring has nothing inside it
    have hz : ∀ x, ¬ G.DiskF ([] : List D) x := by
      rintro x ⟨⟨y, hy, -⟩, -⟩
      simp at hy
    rw [NontrivialRing, faceCard_eq_zero hz] at hnt
    exact absurd hnt.1 (Nat.not_lt_zero m)
  · -- a one-dart ring is a bridge
    have h : G.CFace (G.edge a) a := isCyclicChain_singleton.mp hscyc.isCyclicChain
    exact absurd h.symm (hbridge a)
  · -- an edge orbit has nothing outside it
    by_contra hcon
    rw [properRing_pair, not_not] at hcon
    have hedge : ∀ z ∈ [a, b], G.edge z ∈ [a, b] := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [hcon]; simp
      · rw [List.mem_singleton] at hz
        subst hz
        rw [← hcon, hplain.edge_edge]
        simp
    -- the disk of an edge orbit is closed under every contour step
    have step : ∀ (p : List D) (z : D), List.IsChain G.Clink (z :: p) →
        G.DiskN [a, b] z → G.DiskN [a, b] (p.getLastD z) := by
      intro p
      induction p with
      | nil => intro z _ hz; exact hz
      | cons w p ih =>
        intro z hchain hz
        obtain ⟨hzw, htail⟩ := List.isChain_cons_cons.mp hchain
        rw [getLastD_cons]
        refine ih w htail ?_
        rcases hzw with h | h
        · subst h
          exact diskN_node_iff.mp hz
        · subst h
          have h2 : G.DiskN [a, b] (G.edge z) := by
            by_cases hzr : z ∈ [a, b]
            · exact diskN_of_mem (hedge z hzr)
            · exact (diskE_edge hplan hscyc ⟨hz, hzr⟩).1
          rw [← diskN_node_iff, hplain.node_face]
          exact h2
    have hall : ∀ z, G.DiskN [a, b] z := by
      intro z
      obtain ⟨p, hchain, hlast⟩ := G.connected_clink_list hconn a z
      rw [← getLastD_of_getLast a p hlast]
      exact step p a hchain (diskN_of_mem (by simp))
    have hz : ∀ x, ¬ G.DiskFC [a, b] x := fun x h => h.1 (hall x)
    rw [NontrivialRing, faceCard_eq_zero hz] at hnt
    exact absurd hnt.2 (Nat.not_lt_zero m)
  · trivial

/-- The reverse of a nontrivial ring is nontrivial, with the two sides
exchanged. -/
theorem nontrivial_revRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) {m : ℕ}
    (hnt : G.NontrivialRing m r) : G.NontrivialRing m (G.revRing r) := by
  have hproper := nontrivialRing_properRing hplan hplain hbridge hconn hscyc hnt
  constructor
  · rw [faceCard_congr fun x => diskF_revRing hplan hplain hconn hscyc hproper (x := x)]
    exact hnt.2
  · rw [faceCard_congr fun x => diskFC_revRing hplan hplain hconn hscyc hproper (x := x)]
    exact hnt.1

end NontrivialProper

/-! ### Chord rings

A *chord* of a ring `r` is a dart `x` with both `x` and `edge x` in the face
band of `r`.  It cuts `r` into two arcs, and closing each arc with the chord
gives the two *chord rings* of `x` and of `edge x`. -/

section ChordRing

variable [Finite D] {G : Hypermap D} {r : List D}

open scoped Classical in
/-- The ring cut off by a chord `x` of `r`: the chord, followed by the arc of
`r` running from the face of `edge x` back to the face of `x`. -/
noncomputable def chordRing (G : Hypermap D) (r : List D) (x : D) : List D :=
  x :: arc r (G.fproj r (G.edge x)) (G.fproj r x)

omit [Finite D] in
/-- **A chord splits its ring into two arcs**, one for each of the two chord
rings. -/
theorem exists_chordRing_split (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) :
    ∃ p q : List D,
      G.chordRing r x = x :: G.fproj r (G.edge x) :: p ∧
      G.chordRing r (G.edge x) = G.edge x :: G.fproj r x :: q ∧
      ∃ n, r.rotate n = (G.fproj r (G.edge x) :: p) ++ (G.fproj r x :: q) := by
  classical
  have hne : G.fproj r (G.edge x) ≠ G.fproj r x := by
    intro heq
    exact hbridge x ((G.cface_fproj x).trans (heq ▸ G.cface_fproj (G.edge x)).symm)
  obtain ⟨p, q, h1, h2, n, hn⟩ :=
    exists_arc_split hscyc.nodup (G.fproj_mem hexb) (G.fproj_mem hxb) hne
  refine ⟨p, q, by simp only [chordRing, h1], ?_, n, hn⟩
  simp only [chordRing, hplain.edge_edge, h2]

omit [Finite D] in
/-- A chord ring is a face-simple R-cycle. -/
theorem scycle_chordRing (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) :
    G.Scycle G.Rlink (G.chordRing r x) := by
  obtain ⟨p, q, hcr1, -, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  have hcycAB : IsCyclicChain G.Rlink
      ((G.fproj r (G.edge x) :: p) ++ (G.fproj r x :: q)) := by
    rw [← hn]; exact isCyclicChain_rotate.mpr hscyc.isCyclicChain
  have hsimAB : G.Simple ((G.fproj r (G.edge x) :: p) ++ (G.fproj r x :: q)) := by
    rw [← hn]; exact simple_rotate.mpr hscyc.simple
  obtain ⟨hchainA, -, hlink⟩ := List.isChain_append.mp hcycAB.isChain
  obtain ⟨hsimA, -, hdisjband⟩ := simple_append.mp hsimAB
  have hlast : G.Rlink (p.getLastD (G.fproj r (G.edge x))) (G.fproj r x) :=
    hlink _ (getLast?_cons_eq_some _ p) _ rfl
  rw [hcr1]
  constructor
  · refine isCyclicChain_cons.mpr
      ⟨List.IsChain.cons_cons (G.cface_fproj (G.edge x)) hchainA, ?_⟩
    rw [getLast_cons_eq_getLastD, getLastD_cons]
    exact (rlink_congr_right (G.cface_fproj x).symm _).mp hlast
  · refine simple_cons.mpr ⟨?_, hsimA⟩
    rintro ⟨z, hz, hxz⟩
    exact hdisjband z hz ⟨G.fproj r x, List.mem_cons_self, hxz.symm.trans (G.cface_fproj x)⟩

/-- The chord ring of a chord in the interior of the ring is proper. -/
theorem properRing_chordRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hdEx : G.DiskE r x) (hxb : G.Fband r x)
    (hexb : G.Fband r (G.edge x)) : G.ProperRing (G.chordRing r x) := by
  obtain ⟨p, q, hcr1, -, -⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  have hexr : G.edge x ∉ r := ((diskE_edge_iff hplan hscyc).mpr hdEx).2
  rw [hcr1]
  rcases p with _ | ⟨z, p⟩
  · rw [properRing_pair]
    exact fun heq => hexr (by rw [heq]; exact G.fproj_mem hexb)
  · trivial

omit [Finite D] in
/-- The chord itself lies on its chord ring. -/
theorem head_mem_chordRing (G : Hypermap D) (r : List D) (x : D) : x ∈ G.chordRing r x :=
  List.mem_cons_self

omit [Finite D] in
open scoped Classical in
/-- Membership in a chord ring. -/
theorem mem_chordRing_iff {x z : D} :
    z ∈ G.chordRing r x ↔ z = x ∨ z ∈ arc r (G.fproj r (G.edge x)) (G.fproj r x) :=
  List.mem_cons

omit [Finite D] in
open scoped Classical in
/-- Apart from the chord, the darts of a chord ring are darts of the ring. -/
theorem mem_of_mem_chordRing {x z : D} (h : z ∈ G.chordRing r x) (hne : z ≠ x) : z ∈ r :=
  mem_of_mem_arc ((mem_chordRing_iff.mp h).resolve_left hne)

/-- The invariant of the contour induction below: the two chord rings of a
chord split the disk of the ring between them. -/
def ChordSplit (G : Hypermap D) (r : List D) (x y : D) : Prop :=
  (G.DiskN (G.chordRing r x) y ∨ G.DiskN (G.chordRing r (G.edge x)) y ↔ G.DiskN r y) ∧
    ¬ (G.DiskN (G.chordRing r x) y ∧ G.DiskN (G.chordRing r (G.edge x)) y)

/-- The chord splitting is invariant along node orbits. -/
theorem chordSplit_node {x y : D} : G.ChordSplit r x (G.node y) ↔ G.ChordSplit r x y := by
  simp only [ChordSplit, diskN_node_iff]

/-- The chord lies in its own chord ring and outside the other one. -/
theorem chordSplit_self (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hdEx : G.DiskE r x) (hxb : G.Fband r x)
    (hexb : G.Fband r (G.edge x)) : G.ChordSplit r x x := by
  have hdEex : G.DiskE r (G.edge x) := (diskE_edge_iff hplan hscyc).mpr hdEx
  have hscyc2 : G.Scycle G.Rlink (G.chordRing r (G.edge x)) :=
    scycle_chordRing hplain hbridge hscyc hexb (by rw [hplain.edge_edge]; exact hxb)
  have hxcr2 : x ∉ G.chordRing r (G.edge x) := fun hc =>
    hdEx.2 (mem_of_mem_chordRing hc fun h => hplain.edge_ne x h.symm)
  have hN2x : ¬ G.DiskN (G.chordRing r (G.edge x)) x := fun hc =>
    ((diskE_edge_iff hplan hscyc2).mpr ⟨hc, hxcr2⟩).2 (G.head_mem_chordRing r (G.edge x))
  exact ⟨iff_of_true (Or.inl (diskN_of_mem (G.head_mem_chordRing r x))) hdEx.1,
    fun h => hN2x h.2⟩

/-- The edge of the chord lies in the other chord ring only. -/
theorem chordSplit_edge_self (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hdEx : G.DiskE r x) (hxb : G.Fband r x)
    (hexb : G.Fband r (G.edge x)) : G.ChordSplit r x (G.edge x) := by
  have hdEex : G.DiskE r (G.edge x) := (diskE_edge_iff hplan hscyc).mpr hdEx
  have hscyc1 : G.Scycle G.Rlink (G.chordRing r x) :=
    scycle_chordRing hplain hbridge hscyc hxb hexb
  have hexcr1 : G.edge x ∉ G.chordRing r x := fun hc =>
    hdEex.2 (mem_of_mem_chordRing hc fun h => hplain.edge_ne x h)
  have hN1ex : ¬ G.DiskN (G.chordRing r x) (G.edge x) := fun hc =>
    ((diskE_edge_iff hplan hscyc1).mp ⟨hc, hexcr1⟩).2 (G.head_mem_chordRing r x)
  exact ⟨iff_of_true (Or.inr (diskN_of_mem (G.head_mem_chordRing r (G.edge x)))) hdEex.1,
    fun h => hN1ex h.1⟩

/-- The chord splitting is carried across edges: this is the inductive step of
`diskN_chordRing`. -/
theorem chordSplit_edge (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D} (hdEx : G.DiskE r x)
    (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) {y : D}
    (hy : G.ChordSplit r x y) : G.ChordSplit r x (G.edge y) := by
  obtain ⟨p, q, hcr1, hcr2, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  set A := G.fproj r (G.edge x) :: p with hA
  set B := G.fproj r x :: q with hB
  have hmemr : ∀ z : D, z ∈ r ↔ z ∈ A ∨ z ∈ B := by
    intro z
    constructor
    · intro hz
      rw [← List.mem_append, ← hn]
      exact List.mem_rotate.mpr hz
    · intro hz
      have h2 : z ∈ r.rotate n := by rw [hn, List.mem_append]; exact hz
      exact List.mem_rotate.mp h2
  have hnodupAB : (A ++ B).Nodup := by rw [← hn]; exact List.nodup_rotate.mpr hscyc.nodup
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnodupAB
  have hdEex : G.DiskE r (G.edge x) := (diskE_edge_iff hplan hscyc).mpr hdEx
  have hxne : x ≠ G.edge x := fun h => hplain.edge_ne x h.symm
  have hmem1 : ∀ z : D, z ∈ G.chordRing r x ↔ z = x ∨ z ∈ A := by
    intro z; rw [hcr1]; exact List.mem_cons
  have hmem2 : ∀ z : D, z ∈ G.chordRing r (G.edge x) ↔ z = G.edge x ∨ z ∈ B := by
    intro z; rw [hcr2]; exact List.mem_cons
  have hE1 : ∀ z : D, G.DiskE (G.chordRing r x) (G.edge z) ↔ G.DiskE (G.chordRing r x) z :=
    fun _ => diskE_edge_iff hplan (scycle_chordRing hplain hbridge hscyc hxb hexb)
  have hE2 : ∀ z : D, G.DiskE (G.chordRing r (G.edge x)) (G.edge z) ↔
      G.DiskE (G.chordRing r (G.edge x)) z := fun _ =>
    diskE_edge_iff hplan
      (scycle_chordRing hplain hbridge hscyc hexb (by rw [hplain.edge_edge]; exact hxb))
  have hEr : ∀ z : D, G.DiskE r (G.edge z) ↔ G.DiskE r z := fun _ => diskE_edge_iff hplan hscyc
  by_cases hyx : y = x
  · subst hyx
    exact chordSplit_edge_self hplan hplain hbridge hscyc hdEx hxb hexb
  by_cases hyex : y = G.edge x
  · subst hyex
    rw [hplain.edge_edge]
    exact chordSplit_self hplan hplain hbridge hscyc hdEx hxb hexb
  by_cases hyr : y ∈ r
  · -- a ring dart: its edge is outside all three disks
    have hnotr : ¬ G.DiskN r (G.edge y) := diskN_edge_ring hplan hplain hscyc hproper hyr
    have heyr : G.edge y ∉ r := fun hc => hnotr (diskN_of_mem hc)
    have hey1 : G.edge y ∉ G.chordRing r x := by
      rw [hmem1]
      rintro (h | h)
      · exact hyex (by rw [← hplain.edge_edge y, h])
      · exact heyr ((hmemr _).mpr (Or.inl h))
    have hey2 : G.edge y ∉ G.chordRing r (G.edge x) := by
      rw [hmem2]
      rintro (h | h)
      · exact hyx (G.edge.injective h)
      · exact heyr ((hmemr _).mpr (Or.inr h))
    have hycr : y ∈ G.chordRing r x ∨ y ∈ G.chordRing r (G.edge x) := by
      rcases (hmemr y).mp hyr with h | h
      · exact Or.inl ((hmem1 y).mpr (Or.inr h))
      · exact Or.inr ((hmem2 y).mpr (Or.inr h))
    have hn1 : ¬ G.DiskN (G.chordRing r x) (G.edge y) := by
      intro hc
      have h1 : G.DiskE (G.chordRing r x) y := (hE1 y).mp ⟨hc, hey1⟩
      rcases hycr with h | h
      · exact h1.2 h
      · exact hy.2 ⟨h1.1, diskN_of_mem h⟩
    have hn2 : ¬ G.DiskN (G.chordRing r (G.edge x)) (G.edge y) := by
      intro hc
      have h1 : G.DiskE (G.chordRing r (G.edge x)) y := (hE2 y).mp ⟨hc, hey2⟩
      rcases hycr with h | h
      · exact hy.2 ⟨diskN_of_mem h, h1.1⟩
      · exact h1.2 h
    exact ⟨iff_of_false (fun h => h.elim hn1 hn2) hnotr, fun h => hn1 h.1⟩
  · -- a dart off the ring that is neither the chord nor its edge
    have hy1 : y ∉ G.chordRing r x := by
      rw [hmem1]
      rintro (h | h)
      · exact hyx h
      · exact hyr ((hmemr _).mpr (Or.inl h))
    have hy2 : y ∉ G.chordRing r (G.edge x) := by
      rw [hmem2]
      rintro (h | h)
      · exact hyex h
      · exact hyr ((hmemr _).mpr (Or.inr h))
    have hEy1 : G.DiskN (G.chordRing r x) y ↔ G.DiskE (G.chordRing r x) y :=
      ⟨fun h => ⟨h, hy1⟩, fun h => h.1⟩
    have hEy2 : G.DiskN (G.chordRing r (G.edge x)) y ↔
        G.DiskE (G.chordRing r (G.edge x)) y := ⟨fun h => ⟨h, hy2⟩, fun h => h.1⟩
    have hEyr : G.DiskN r y ↔ G.DiskE r y := ⟨fun h => ⟨h, hyr⟩, fun h => h.1⟩
    have heyx : G.edge y ≠ x := fun h => hyex (by rw [← hplain.edge_edge y, h])
    have heyex : G.edge y ≠ G.edge x := fun h => hyx (G.edge.injective h)
    by_cases heyr : G.edge y ∈ r
    · -- the edge of `y` lands on the ring, on exactly one of the two arcs
      have hnry : ¬ G.DiskN r y := fun hc => ((hEr y).mpr (hEyr.mp hc)).2 heyr
      have hn1y : ¬ G.DiskN (G.chordRing r x) y := fun hc => hnry (hy.1.mp (Or.inl hc))
      have hn2y : ¬ G.DiskN (G.chordRing r (G.edge x)) y := fun hc => hnry (hy.1.mp (Or.inr hc))
      rcases (hmemr _).mp heyr with hAe | hBe
      · have h1 : G.DiskN (G.chordRing r x) (G.edge y) :=
          diskN_of_mem ((hmem1 _).mpr (Or.inr hAe))
        have h2 : ¬ G.DiskN (G.chordRing r (G.edge x)) (G.edge y) := by
          intro hc
          have hey2 : G.edge y ∉ G.chordRing r (G.edge x) := by
            rw [hmem2]
            rintro (h | h)
            · exact heyex h
            · exact hdisj _ hAe _ h rfl
          exact hn2y ((hE2 y).mp ⟨hc, hey2⟩).1
        exact ⟨iff_of_true (Or.inl h1) (diskN_of_mem heyr), fun h => h2 h.2⟩
      · have h2 : G.DiskN (G.chordRing r (G.edge x)) (G.edge y) :=
          diskN_of_mem ((hmem2 _).mpr (Or.inr hBe))
        have h1 : ¬ G.DiskN (G.chordRing r x) (G.edge y) := by
          intro hc
          have hey1 : G.edge y ∉ G.chordRing r x := by
            rw [hmem1]
            rintro (h | h)
            · exact heyx h
            · exact hdisj _ h _ hBe rfl
          exact hn1y ((hE1 y).mp ⟨hc, hey1⟩).1
        exact ⟨iff_of_true (Or.inr h2) (diskN_of_mem heyr), fun h => h1 h.1⟩
    · -- the edge of `y` is off the ring too: nothing changes
      have hey1 : G.edge y ∉ G.chordRing r x := by
        rw [hmem1]
        rintro (h | h)
        · exact heyx h
        · exact heyr ((hmemr _).mpr (Or.inl h))
      have hey2 : G.edge y ∉ G.chordRing r (G.edge x) := by
        rw [hmem2]
        rintro (h | h)
        · exact heyex h
        · exact heyr ((hmemr _).mpr (Or.inr h))
      have e1 : G.DiskN (G.chordRing r x) (G.edge y) ↔ G.DiskN (G.chordRing r x) y :=
        ⟨fun h => hEy1.mpr ((hE1 y).mp ⟨h, hey1⟩), fun h => ((hE1 y).mpr (hEy1.mp h)).1⟩
      have e2 : G.DiskN (G.chordRing r (G.edge x)) (G.edge y) ↔
          G.DiskN (G.chordRing r (G.edge x)) y :=
        ⟨fun h => hEy2.mpr ((hE2 y).mp ⟨h, hey2⟩), fun h => ((hE2 y).mpr (hEy2.mp h)).1⟩
      have er : G.DiskN r (G.edge y) ↔ G.DiskN r y :=
        ⟨fun h => hEyr.mpr ((hEr y).mp ⟨h, heyr⟩), fun h => ((hEr y).mpr (hEyr.mp h)).1⟩
      exact ⟨by rw [e1, e2, er]; exact hy.1, by rw [e1, e2]; exact hy.2⟩

/-- **The two chord rings of a chord split the disk of the ring.** -/
theorem chordSplit_all (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D}
    (hdEx : G.DiskE r x) (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) (y : D) :
    G.ChordSplit r x y := by
  have step : ∀ (pth : List D) (z : D), List.IsChain G.Clink (z :: pth) →
      G.ChordSplit r x z → G.ChordSplit r x (pth.getLastD z) := by
    intro pth
    induction pth with
    | nil => intro z _ hz; exact hz
    | cons w pth ih =>
      intro z hchain hz
      obtain ⟨hzw, htail⟩ := List.isChain_cons_cons.mp hchain
      rw [getLastD_cons]
      refine ih w htail ?_
      rcases hzw with h | h
      · subst h
        exact chordSplit_node.mp hz
      · subst h
        rw [← chordSplit_node, hplain.node_face]
        exact chordSplit_edge hplan hplain hbridge hscyc hproper hdEx hxb hexb hz
  obtain ⟨pth, hchain, hlast⟩ := G.connected_clink_list hconn x y
  rw [← getLastD_of_getLast x pth hlast]
  exact step pth x hchain (chordSplit_self hplan hplain hbridge hscyc hdEx hxb hexb)

/-- **The disk of a chord ring is the part of the disk missed by the other
chord ring.** -/
theorem diskN_chordRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D}
    (hdEx : G.DiskE r x) (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) {y : D} :
    G.DiskN (G.chordRing r x) y ↔
      G.DiskN r y ∧ ¬ G.DiskN (G.chordRing r (G.edge x)) y := by
  obtain ⟨h1, h2⟩ :=
    chordSplit_all hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb y
  constructor
  · exact fun h => ⟨h1.mp (Or.inl h), fun hc => h2 ⟨h, hc⟩⟩
  · rintro ⟨hr, hnc⟩
    exact (h1.mpr hr).resolve_right hnc

/-- The face-closed disk only depends on the face of a dart. -/
theorem diskF_congr {s : List D} {u v : D} (h : G.CFace u v) : G.DiskF s u ↔ G.DiskF s v := by
  replace h := (sameCycle_iff_reflTransGen G.face u v).mp h
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (by rw [hbc]; exact diskF_face_iff.symm)

omit [Finite D] in
/-- **The two chord rings of a chord split the face band of the ring.** -/
theorem fband_chordRing (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hscyc : G.Scycle G.Rlink r) {x : D} (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x))
    {y : D} : (G.Fband (G.chordRing r x) y ∨ G.Fband (G.chordRing r (G.edge x)) y) ↔
      G.Fband r y := by
  obtain ⟨p, q, hcr1, hcr2, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  have hbr : G.Fband r y ↔ G.Fband (G.fproj r (G.edge x) :: p) y ∨
      G.Fband (G.fproj r x :: q) y := by
    rw [← fband_rotate (n := n), hn, fband_append]
  rw [hcr1, hcr2, hbr]
  constructor
  · rintro (h | h)
    · rcases fband_cons.mp h with h | h
      · exact Or.inr ⟨G.fproj r x, List.mem_cons_self, h.trans (G.cface_fproj x)⟩
      · exact Or.inl h
    · rcases fband_cons.mp h with h | h
      · exact Or.inl ⟨G.fproj r (G.edge x), List.mem_cons_self,
          h.trans (G.cface_fproj (G.edge x))⟩
      · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (fband_cons.mpr (Or.inr h))
    · exact Or.inr (fband_cons.mpr (Or.inr h))

/-- **The face-closed disk of a chord ring is the part of the face-closed disk
missed by the other chord ring.** -/
theorem diskF_chordRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D}
    (hdEx : G.DiskE r x) (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x)) {y : D} :
    G.DiskF (G.chordRing r x) y ↔
      G.DiskF r y ∧ ¬ G.DiskF (G.chordRing r (G.edge x)) y := by
  by_cases hb2 : G.Fband (G.chordRing r (G.edge x)) y
  · -- `y` lies in the band of the other chord ring, so neither side holds
    obtain ⟨z, hz, hyz⟩ := hb2
    have hbr : G.Fband r y := (fband_chordRing hplain hbridge hscyc hxb hexb).mp
      (Or.inr ⟨z, hz, hyz⟩)
    refine iff_of_false (fun hc => ?_) (fun hc => hc.1.2 hbr)
    have hFz : G.DiskF (G.chordRing r x) z := (diskF_congr hyz).mp hc
    exact (chordSplit_all hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb z).2
      ⟨hFz.1, diskN_of_mem hz⟩
  · -- otherwise the two bands agree and the disks split
    have hbr : G.Fband (G.chordRing r x) y ↔ G.Fband r y :=
      ⟨fun h => (fband_chordRing hplain hbridge hscyc hxb hexb).mp (Or.inl h),
        fun h => ((fband_chordRing hplain hbridge hscyc hxb hexb).mpr h).resolve_right hb2⟩
    constructor
    · rintro ⟨hN, hb1⟩
      rw [diskN_chordRing hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb] at hN
      exact ⟨⟨hN.1, fun h => hb1 (hbr.mpr h)⟩, fun hc => hN.2 hc.1⟩
    · rintro ⟨⟨hNr, hbr'⟩, hnd2⟩
      exact ⟨(diskN_chordRing hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb).mpr
        ⟨hNr, fun hc => hnd2 ⟨hc, hb2⟩⟩, fun hc => hbr' (hbr.mp hc)⟩

/-- **A chord ring with a face inside it and a long complementary arc is a
strictly shorter nontrivial ring.** -/
theorem nontrivial_chordRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {x : D}
    (hdEx : G.DiskE r x) (hxb : G.Fband r x) (hexb : G.Fband r (G.edge x))
    (hlen : 2 < (G.chordRing r (G.edge x)).length)
    (hface : ∃ y, G.DiskF (G.chordRing r x) y) :
    G.NontrivialRing 0 (G.chordRing r x) ∧ (G.chordRing r x).length < r.length := by
  obtain ⟨p, q, hcr1, hcr2, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  rw [hcr2] at hlen
  simp only [List.length_cons] at hlen
  rcases q with _ | ⟨x3, q'⟩
  · simp at hlen
  -- the lengths
  have hlenr : r.length = (p.length + 1) + (q'.length + 1 + 1) := by
    have h := congrArg List.length hn
    rw [List.length_rotate] at h
    simp only [List.length_append, List.length_cons] at h
    omega
  have hlen1 : (G.chordRing r x).length = p.length + 1 + 1 := by
    rw [hcr1]; simp
  refine ⟨?_, by omega⟩
  -- the witness outside the chord ring
  have hnodupAB : ((G.fproj r (G.edge x) :: p) ++ (G.fproj r x :: x3 :: q')).Nodup := by
    rw [← hn]; exact List.nodup_rotate.mpr hscyc.nodup
  obtain ⟨-, hnodupB, hdisj⟩ := List.nodup_append.mp hnodupAB
  have hmemr : ∀ z : D, z ∈ (G.fproj r (G.edge x) :: p) ∨ z ∈ (G.fproj r x :: x3 :: q') →
      z ∈ r := by
    intro z hz
    exact List.mem_rotate.mp (by rw [hn, List.mem_append]; exact hz)
  have hx3B : x3 ∈ (G.fproj r x :: x3 :: q') := List.mem_cons_of_mem _ List.mem_cons_self
  have hx3r : x3 ∈ r := hmemr x3 (Or.inr hx3B)
  have hx3cr2 : x3 ∈ G.chordRing r (G.edge x) := by rw [hcr2]; exact List.mem_cons_of_mem _ hx3B
  refine nontrivialRing_zero_iff.mpr ⟨hface, x3, ?_, ?_⟩
  · exact fun hc =>
      (chordSplit_all hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb x3).2
        ⟨hc, diskN_of_mem hx3cr2⟩
  · rw [hcr1, fband_cons]
    rintro (h | ⟨w, hw, hx3w⟩)
    · -- `x3` would share a face with the chord, hence with `fproj r x`
      have h1 : G.CFace x3 (G.fproj r x) := h.trans (G.cface_fproj x)
      have h2 : x3 = G.fproj r x :=
        hscyc.simple.eq_of_cface hx3r (hmemr _ (Or.inr List.mem_cons_self)) h1
      exact (List.nodup_cons.mp hnodupB).1 (by rw [← h2]; exact List.mem_cons_self)
    · -- `x3` would share a face with a dart of the other arc
      have h2 : x3 = w := hscyc.simple.eq_of_cface hx3r (hmemr w (Or.inl hw)) hx3w
      exact hdisj w hw x3 hx3B h2.symm

/-- The form of `nontrivial_chordRing` used when the two ends of the chord are
not cyclically consecutive on the ring. -/
theorem nontrivial_chordRing_of_not_cyclicNext (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r)
    (hproper : G.ProperRing r) {x : D} (hdEx : G.DiskE r x) (hxb : G.Fband r x)
    (hexb : G.Fband r (G.edge x))
    (hnc : ¬ CyclicNext r (G.fproj r x) (G.fproj r (G.edge x)))
    (hface : ∃ y, G.DiskF (G.chordRing r x) y) :
    G.NontrivialRing 0 (G.chordRing r x) ∧ (G.chordRing r x).length < r.length := by
  refine nontrivial_chordRing hplan hplain hbridge hconn hscyc hproper hdEx hxb hexb ?_ hface
  obtain ⟨p, q, hcr1, hcr2, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  rw [hcr2]
  simp only [List.length_cons]
  by_contra hcon
  have hq : q = [] := List.length_eq_zero_iff.mp (by omega)
  subst hq
  refine hnc ⟨n + (G.fproj r (G.edge x) :: p).length, G.fproj r (G.edge x) :: p, ?_, rfl⟩
  rw [← List.rotate_rotate, hn, List.rotate_append_length_eq]
  rfl

end ChordRing

/-! ### Cutting along the reverse ring

Cutting `G` along `revRing r` gives a second disk-and-remainder pair, whose
disk covers exactly the darts that the disk of `r` misses. -/

section RevSnipMaps

variable [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

/-- The disk map of the reverse cut: its darts are the exact complement of
`DiskN r`. -/
noncomputable def revSnipDisk (G : Hypermap D) (r : List D) (hplan : G.Planar)
    (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r) :
    Hypermap {z : D // G.DiskN (G.revRing r) z} :=
  snipDisk G (G.revRing r) hplan (scycle_revRing hplain hscyc)

/-- The remainder map of the reverse cut. -/
noncomputable def revSnipRem (G : Hypermap D) (r : List D) (hplan : G.Planar)
    (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r) :
    Hypermap {z : D // ¬ G.DiskE (G.revRing r) z} :=
  snipRem G (G.revRing r) hplan (scycle_revRing hplain hscyc)

/-- The border ring of the reverse disk map. -/
def revSnipdRing (G : Hypermap D) (r : List D) :
    List {z : D // G.DiskN (G.revRing r) z} :=
  G.snipdRing (G.revRing r)

/-- The border ring of the reverse remainder map. -/
def revSniprRing (G : Hypermap D) (r : List D) :
    List {z : D // ¬ G.DiskE (G.revRing r) z} :=
  G.sniprRing (G.revRing r)

omit [DecidableEq D] in
/-- The border of the reverse disk map projects onto the reverse ring. -/
@[simp] theorem map_revSnipdRing :
    (G.revSnipdRing r).map (G.snipd (G.revRing r)) = G.revRing r :=
  map_snipdRing

omit [Finite D] [DecidableEq D] in
/-- The border of the reverse remainder map projects onto the edges of the
ring. -/
@[simp] theorem map_revSniprRing :
    (G.revSniprRing r).map (G.snipr (G.revRing r)) = r.map G.edge := by
  rw [revSniprRing, map_sniprRing, revRing, List.reverse_reverse]

/-- **Cutting along the reverse ring** exhibits `G` as a patch of the reverse
disk map and the reverse remainder map. -/
theorem revSnip_patch (hplan : G.Planar) (hplain : G.Plain) (hscyc : G.Scycle G.Rlink r) :
    Patch G (G.revSnipDisk r hplan hplain hscyc) (G.revSnipRem r hplan hplain hscyc)
      (G.snipd (G.revRing r)) (G.snipr (G.revRing r))
      (G.revSnipdRing r) (G.revSniprRing r) :=
  snip_patch hplan (scycle_revRing hplain hscyc)

/-- The reverse disk map of a planar map is planar. -/
theorem planar_revSnipDisk (hplan : G.Planar) (hplain : G.Plain)
    (hscyc : G.Scycle G.Rlink r) : (G.revSnipDisk r hplan hplain hscyc).Planar :=
  planar_snipDisk hplan (scycle_revRing hplain hscyc)

/-- The reverse remainder map of a planar map is planar. -/
theorem planar_revSnipRem (hplan : G.Planar) (hplain : G.Plain)
    (hscyc : G.Scycle G.Rlink r) : (G.revSnipRem r hplan hplain hscyc).Planar :=
  planar_snipRem hplan (scycle_revRing hplain hscyc)

end RevSnipMaps

/-! ### Chords of the border of the disk map

A chord of the border ring of the disk map gives a chord of the ring in `G`,
and hence a strictly shorter nontrivial ring. -/

section RingDiskChord

variable [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

/-- **A chorded disk border yields a strictly shorter nontrivial ring.** -/
theorem ring_disk_chord (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hconn : G.Connected) (hscyc : G.Scycle G.Rlink r) {m : ℕ} (hnt : G.NontrivialRing m r)
    (hchord : ¬ (snipDisk G r hplan hscyc).Chordless (G.snipdRing r)) :
    ∃ r' : List D, G.Scycle G.Rlink r' ∧ G.NontrivialRing 0 r' ∧ r'.length < r.length := by
  have hproper := nontrivialRing_properRing hplan hplain hbridge hconn hscyc hnt
  set Gd := snipDisk G r hplan hscyc with hGd
  -- extract the chord of the border ring
  obtain ⟨xd, hxd, yd, hyd, hadj, hno⟩ : ∃ xd ∈ G.snipdRing r, ∃ yd ∈ G.snipdRing r,
      Gd.Adj xd yd ∧ ¬ (yd = xd ∨ CyclicNext (G.snipdRing r) xd yd ∨
        CyclicNext (G.snipdRing r) yd xd) := by
    by_contra hc
    refine hchord fun xd hxd yd hyd hadj => ?_
    by_contra hno
    exact hc ⟨xd, hxd, yd, hyd, hadj, hno⟩
  have hnc1 : ¬ CyclicNext (G.snipdRing r) xd yd := fun h => hno (Or.inr (Or.inl h))
  have hnc2 : ¬ CyclicNext (G.snipdRing r) yd xd := fun h => hno (Or.inr (Or.inr h))
  obtain ⟨zd, hxz, hzy⟩ := hadj
  have hxr : G.snipd r xd ∈ r := mem_snipdRing.mp hxd
  have hyr : G.snipd r yd ∈ r := mem_snipdRing.mp hyd
  -- the chord in `G` and its two ends on the ring
  have hCFxz : G.CFace (G.snipd r xd) (G.snipd r zd) := cface_snipd hplan hscyc hxz
  have hCFwy : G.CFace (G.snipd r (Gd.face (Gd.edge zd))) (G.snipd r yd) :=
    cface_snipd hplan hscyc ((Gd.cface_face (Gd.edge zd)).symm.trans hzy)
  have hnodew : G.node (G.snipd r (Gd.face (Gd.edge zd))) = G.snipd r zd := by
    have h1 : G.snipd r (Gd.node (Gd.face (Gd.edge zd)))
        = G.node (G.snipd r (Gd.face (Gd.edge zd))) := rfl
    rw [← h1, Gd.edgeK zd]
  have hface_edge : G.face (G.edge (G.snipd r zd)) = G.snipd r (Gd.face (Gd.edge zd)) :=
    G.node.injective (by rw [G.edgeK, hnodew])
  have hRzy : G.Rlink (G.snipd r zd) (G.snipd r yd) :=
    (G.cface_face (G.edge (G.snipd r zd))).trans (by rw [hface_edge]; exact hCFwy)
  have hbz : G.Fband r (G.snipd r zd) := ⟨G.snipd r xd, hxr, hCFxz.symm⟩
  have hbez : G.Fband r (G.edge (G.snipd r zd)) := ⟨G.snipd r yd, hyr, hRzy⟩
  have hfpz : G.fproj r (G.snipd r zd) = G.snipd r xd :=
    hscyc.simple.fproj_eq hxr hCFxz.symm
  have hfpez : G.fproj r (G.edge (G.snipd r zd)) = G.snipd r yd :=
    hscyc.simple.fproj_eq hyr hRzy
  -- the chord is in the interior of the ring
  have hznr : G.snipd r zd ∉ r := by
    intro hzr
    have hxz' : G.snipd r xd = G.snipd r zd := hscyc.simple.eq_of_cface hxr hzr hCFxz
    obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hzr
    have hmod : (i + 1) % r.length < r.length := Nat.mod_lt _ (by omega)
    have hlink : G.CFace (G.edge r[i]) r[(i + 1) % r.length] :=
      rel_getElem_succ hscyc.isCyclicChain hi hmod rfl
    rw [hri] at hlink
    have hy' : G.snipd r yd = r[(i + 1) % r.length] :=
      hscyc.simple.eq_of_cface hyr (List.getElem_mem hmod) (hRzy.symm.trans hlink)
    have hcn : CyclicNext r (G.snipd r xd) (G.snipd r yd) := by
      have h0 := cyclicNext_getElem (l := r) hi hmod rfl
      rw [hri, ← hxz', ← hy'] at h0
      exact h0
    exact hnc1 (cyclicNext_of_map (snipd_injective (G := G) (r := r))
      (by rw [map_snipdRing]; exact hcn))
  have hdEz : G.DiskE r (G.snipd r zd) := ⟨zd.2, hznr⟩
  have hdEez : G.DiskE r (G.edge (G.snipd r zd)) := (diskE_edge_iff hplan hscyc).mpr hdEz
  have hbez2 : G.Fband r (G.edge (G.edge (G.snipd r zd))) := by
    rw [hplain.edge_edge]; exact hbz
  -- neither end is the cyclic successor of the other
  have hnc1' : ¬ CyclicNext r (G.fproj r (G.snipd r zd))
      (G.fproj r (G.edge (G.snipd r zd))) := by
    rw [hfpz, hfpez]
    exact fun hcn => hnc1 (cyclicNext_of_map (snipd_injective (G := G) (r := r))
      (by rw [map_snipdRing]; exact hcn))
  have hnc2' : ¬ CyclicNext r (G.fproj r (G.edge (G.snipd r zd)))
      (G.fproj r (G.edge (G.edge (G.snipd r zd)))) := by
    rw [hfpez, hplain.edge_edge, hfpz]
    exact fun hcn => hnc2 (cyclicNext_of_map (snipd_injective (G := G) (r := r))
      (by rw [map_snipdRing]; exact hcn))
  -- a face strictly inside the ring lands in one of the two chord rings
  obtain ⟨t, ht⟩ : ∃ t, G.DiskF r t := by
    refine (zero_lt_faceCard (G := G) (A := G.DiskF r)).mp ?_
    have := hnt.1
    omega
  by_cases hct : G.DiskF (G.chordRing r (G.snipd r zd)) t
  · exact ⟨G.chordRing r (G.snipd r zd), scycle_chordRing hplain hbridge hscyc hbz hbez,
      nontrivial_chordRing_of_not_cyclicNext hplan hplain hbridge hconn hscyc hproper
        hdEz hbz hbez hnc1' ⟨t, hct⟩⟩
  · have hct2 : G.DiskF (G.chordRing r (G.edge (G.snipd r zd))) t := by
      by_contra hc
      exact hct ((diskF_chordRing hplan hplain hbridge hconn hscyc hproper hdEz hbz hbez).mpr
        ⟨ht, hc⟩)
    exact ⟨G.chordRing r (G.edge (G.snipd r zd)),
      scycle_chordRing hplain hbridge hscyc hbez hbez2,
      nontrivial_chordRing_of_not_cyclicNext hplan hplain hbridge hconn hscyc hproper
        hdEez hbez hbez2 hnc2' ⟨t, hct2⟩⟩

end RingDiskChord

/-! ### Faces of the disk map

`Hypermap.cface_snipd` says that the disk projection maps face orbits of the
disk map into face orbits of `G`.  Transferring colourings between the two
sides of the cut needs the converse: a face orbit of `G` meets the disk in a
single face orbit of the disk map.  This is the reference's `cface_snipd`,
which is a `{mono …}` statement. -/

section SnipdFace

variable [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

/-- A face path of `G` leaving a dart whose disk face misses the border ring
stays inside the disk. -/
private theorem cface_snipd_of_not_fband (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {v : {z : D // G.DiskN r z}} :
    ∀ {w : D}, Relation.ReflTransGen (fun a b => b = G.face a) w (G.snipd r v) →
      ∀ u : {z : D // G.DiskN r z}, G.snipd r u = w →
        ¬ (snipDisk G r hplan hscyc).Fband (G.snipdRing r) u →
        (snipDisk G r hplan hscyc).CFace u v := by
  intro w hpath
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro u hu _
    rw [show u = v from Subtype.ext hu]
  | head hwc _ ih =>
    rename_i c _
    intro u hu hnb
    have hur : (u : D) ∉ r := by
      intro hc
      exact hnb ⟨u, mem_snipdRing.mpr hc, SameCycle.refl _ _⟩
    have hstep : (snipDisk G r hplan hscyc).CFace u ((snipDisk G r hplan hscyc).face u) :=
      (snipDisk G r hplan hscyc).cface_face u
    have hval : G.snipd r ((snipDisk G r hplan hscyc).face u) = c := by
      change G.snipdFace r (u : D) = c
      rw [snipdFace_of_not_mem hur, hwc]
      exact congrArg G.face hu
    have hnb' : ¬ (snipDisk G r hplan hscyc).Fband (G.snipdRing r)
        ((snipDisk G r hplan hscyc).face u) := by
      rintro ⟨t, ht, hct⟩
      exact hnb ⟨t, ht, hstep.trans hct⟩
    exact hstep.trans (ih _ hval hnb')

/-- **The disk projection both preserves and reflects face orbits.** -/
theorem cface_snipd_iff (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {u v : {z : D // G.DiskN r z}} :
    (snipDisk G r hplan hscyc).CFace u v ↔ G.CFace (G.snipd r u) (G.snipd r v) := by
  refine ⟨cface_snipd hplan hscyc, fun h => ?_⟩
  by_cases hbu : (snipDisk G r hplan hscyc).Fband (G.snipdRing r) u
  · by_cases hbv : (snipDisk G r hplan hscyc).Fband (G.snipdRing r) v
    · obtain ⟨u1, hu1, hcu1⟩ := hbu
      obtain ⟨v1, hv1, hcv1⟩ := hbv
      have h1 : G.CFace (G.snipd r u1) (G.snipd r v1) :=
        ((cface_snipd hplan hscyc hcu1).symm.trans h).trans (cface_snipd hplan hscyc hcv1)
      have h2 : u1 = v1 := snipd_injective (hscyc.simple.eq_of_cface
        (mem_snipdRing.mp hu1) (mem_snipdRing.mp hv1) h1)
      exact hcu1.trans (h2 ▸ hcv1).symm
    · exact (cface_snipd_of_not_fband hplan hscyc
        ((sameCycle_iff_reflTransGen G.face _ _).mp h.symm) v rfl hbv).symm
  · exact cface_snipd_of_not_fband hplan hscyc
      ((sameCycle_iff_reflTransGen G.face _ _).mp h) u rfl hbu

end SnipdFace

/-! ### Reading a colouring of a submap off the faces of `G`

Transferring a colouring from one side of the cut to the other colours a dart
`w` of `G` by the colour that the given colouring gives to *some* dart of the
submap lying in the face of `w`.  The choice is made through the canonical
representative `froot w` of that face, so that the result only depends on the
face; it is well defined because the projection reflects face orbits. -/

section PickFaceColor

variable [Finite D] {G : Hypermap D}

open scoped Classical in
/-- The colour that a colouring `k` of a submap embedded by `h` gives to the
face of `w`. -/
noncomputable def pickFaceColor {E : Type*} (G : Hypermap D) (h : E → D) (k : E → Color)
    (w : D) : Color :=
  if hex : ∃ u : E, G.CFace (G.froot w) (h u) then k hex.choose else Color.c0

omit [Finite D] in
/-- The colour of a face does not depend on the dart it is read at. -/
theorem pickFaceColor_congr {E : Type*} (h : E → D) (k : E → Color) {w w' : D}
    (hc : G.CFace w w') : G.pickFaceColor h k w = G.pickFaceColor h k w' := by
  unfold pickFaceColor
  rw [G.froot_congr hc]

omit [Finite D] in
/-- Reading the colour at a dart of the submap gives that dart's colour, as
soon as the embedding reflects face orbits and `k` is constant on faces. -/
theorem pickFaceColor_eq {E : Type*} {H : Hypermap E} (h : E → D) (k : E → Color)
    (hkface : ∀ u, k (H.face u) = k u) (hmono : ∀ u v : E, H.CFace u v ↔ G.CFace (h u) (h v))
    {w : D} {u : E} (hw : G.CFace w (h u)) : G.pickFaceColor h k w = k u := by
  have hex : ∃ z : E, G.CFace (G.froot w) (h z) := ⟨u, (G.cface_froot w).symm.trans hw⟩
  unfold pickFaceColor
  rw [dite_eq_left hex]
  refine (congr_of_sameCycle hkface ?_).symm
  exact (hmono u hex.choose).mpr (hw.symm.trans ((G.cface_froot w).trans hex.choose_spec))

end PickFaceColor

/-! ### The two border rings run in step

The border of the disk map of `r` and the border of the remainder map of
`revRing r` traverse the same faces of `G`; rotating the latter by one step
backwards makes the two lists match face by face. -/

section BorderMatch

variable [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

/-- The border ring of the reverse remainder map, rotated so that it runs in
step with the border ring of the disk map. -/
def revSniprRingRot (G : Hypermap D) (r : List D) :
    List {z : D // ¬ G.DiskE (G.revRing r) z} :=
  (G.revSniprRing r).rotate (r.length - 1)

omit [Finite D] [DecidableEq D] in
/-- The rotated reverse border projects onto the rotated edges of the ring. -/
theorem map_revSniprRingRot : (G.revSniprRingRot r).map (G.snipr (G.revRing r))
    = (r.map G.edge).rotate (r.length - 1) := by
  rw [revSniprRingRot, List.map_rotate, map_revSniprRing]

omit [Finite D] [DecidableEq D] in
/-- The rotated reverse border has as many darts as the ring. -/
theorem length_revSniprRingRot : (G.revSniprRingRot r).length = r.length := by
  have h : ((G.revSniprRingRot r).map (G.snipr (G.revRing r))).length
      = ((r.map G.edge).rotate (r.length - 1)).length :=
    congrArg List.length map_revSniprRingRot
  rwa [List.length_map, List.length_rotate, List.length_map] at h

omit [DecidableEq D] in
/-- The border of the disk map has as many darts as the ring. -/
theorem length_snipdRing : (G.snipdRing r).length = r.length := by
  have h : ((G.snipdRing r).map (G.snipd r)).length = r.length :=
    congrArg List.length map_snipdRing
  rwa [List.length_map] at h

omit [Finite D] [DecidableEq D] in
/-- Face by face, the rotated edges of the ring match the ring itself. -/
private theorem cface_getElem_rot (hcyc : IsCyclicChain G.Rlink r) {i : ℕ}
    (hi : i < ((r.map G.edge).rotate (r.length - 1)).length) (hi' : i < r.length) :
    G.CFace ((r.map G.edge).rotate (r.length - 1))[i] r[i] := by
  have hn : 0 < r.length := by omega
  have hlen : (r.map G.edge).length = r.length := by simp
  have hjlt : (i + (r.length - 1)) % (r.map G.edge).length < r.length := by
    rw [hlen]; exact Nat.mod_lt _ hn
  have h1 : ((r.map G.edge).rotate (r.length - 1))[i]
      = G.edge r[(i + (r.length - 1)) % (r.map G.edge).length] := by
    rw [List.getElem_rotate, List.getElem_map]
  have hstep : ((i + (r.length - 1)) % (r.map G.edge).length + 1) % r.length = i := by
    rw [hlen]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hinner : (0 + (r.length - 1)) % r.length = r.length - 1 := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hinner, Nat.sub_add_cancel hn, Nat.mod_self]
    · have hinner : (i + (r.length - 1)) % r.length = i - 1 := by
        rw [show i + (r.length - 1) = (i - 1) + r.length by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hinner, Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hi']
  have hlink : G.CFace (G.edge r[(i + (r.length - 1)) % (r.map G.edge).length])
      r[((i + (r.length - 1)) % (r.map G.edge).length + 1) % r.length] :=
    rel_getElem_succ hcyc hjlt (Nat.mod_lt _ hn) rfl
  rw [h1, ← getElem_congr_idx hstep (Nat.mod_lt _ hn) hi']
  exact hlink

omit [DecidableEq D] in
/-- **The two border rings run in step**: the `i`-th dart of the rotated
reverse border lies in the face of the `i`-th dart of the disk border. -/
theorem cface_getElem_borders (hcyc : IsCyclicChain G.Rlink r) {i : ℕ}
    (h1 : i < (G.revSniprRingRot r).length) (h2 : i < (G.snipdRing r).length) :
    G.CFace (G.snipr (G.revRing r) (G.revSniprRingRot r)[i]) (G.snipd r (G.snipdRing r)[i]) := by
  have hi' : i < r.length := by rw [← length_snipdRing (G := G) (r := r)]; exact h2
  have ha : G.snipr (G.revRing r) (G.revSniprRingRot r)[i]
      = ((r.map G.edge).rotate (r.length - 1))[i]'(by simp; omega) := by
    have h := List.getElem_of_eq (map_revSniprRingRot (G := G) (r := r))
      (show i < ((G.revSniprRingRot r).map (G.snipr (G.revRing r))).length by
        rw [List.length_map]; exact h1)
    rwa [List.getElem_map] at h
  have hb : G.snipd r (G.snipdRing r)[i] = r[i] := by
    have h := List.getElem_of_eq (map_snipdRing (G := G) (r := r))
      (show i < ((G.snipdRing r).map (G.snipd r)).length by rw [List.length_map]; exact h2)
    rwa [List.getElem_map] at h
  rw [ha, hb]
  exact cface_getElem_rot hcyc _ hi'

end BorderMatch

/-! ### Transferring ring traces across the cut

A colouring of the disk of `r` and a colouring of the remainder of
`revRing r` determine each other: the two maps cover `G` between them, and
their border rings run through the same faces of `G`.  This is the reference's
`rev_ring_cotrace`, and it is what makes the ring traces of the disk
Kempe-closed. -/

section RevRingTrace

variable [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

/-- **The ring traces of the disk of `r` are exactly the ring traces of the
remainder of `revRing r`.** -/
theorem rev_ring_cotrace (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) (et : List Color) :
    (snipDisk G r hplan hscyc).RingTrace (G.snipdRing r) et ↔
      (G.revSnipRem r hplan hplain hscyc).RingTrace (G.revSniprRingRot r) et := by
  have hmonoD : ∀ u v : {z : D // G.DiskN r z},
      (snipDisk G r hplan hscyc).CFace u v ↔ G.CFace (G.snipd r u) (G.snipd r v) :=
    fun _ _ => cface_snipd_iff hplan hscyc
  have hmonoR : ∀ u v : {z : D // ¬ G.DiskE (G.revRing r) z},
      (G.revSnipRem r hplan hplain hscyc).CFace u v ↔
        G.CFace (G.snipr (G.revRing r) u) (G.snipr (G.revRing r) v) :=
    fun u v => (revSnip_patch hplan hplain hscyc).cface_hr_iff u v
  constructor
  · -- from the disk of `r` to the remainder of `revRing r`
    rintro ⟨kd, hkd, rfl⟩
    have hpick : ∀ (w : D) (u : {z : D // G.DiskN r z}), G.CFace w (G.snipd r u) →
        G.pickFaceColor (G.snipd r) kd w = kd u :=
      fun _ _ h => pickFaceColor_eq _ _ hkd.face hmonoD h
    -- away from the reverse ring the colour changes across every edge
    have krE : ∀ xr : {z : D // ¬ G.DiskE (G.revRing r) z},
        G.snipr (G.revRing r) xr ∉ G.revRing r →
        G.pickFaceColor (G.snipd r) kd
            (G.snipr (G.revRing r) ((G.revSnipRem r hplan hplain hscyc).edge xr))
          ≠ G.pickFaceColor (G.snipd r) kd (G.snipr (G.revRing r) xr) := by
      intro xr hxr
      have hxN : G.DiskN r (G.snipr (G.revRing r) xr) := by
        have h1 : ¬ G.DiskN (G.revRing r) (G.snipr (G.revRing r) xr) := fun hc => xr.2 ⟨hc, hxr⟩
        rw [diskN_revRing hplan hplain hconn hscyc hproper] at h1
        exact not_not.mp h1
      set xd : {z : D // G.DiskN r z} := ⟨G.snipr (G.revRing r) xr, hxN⟩ with hxd
      have hnode : G.node (G.snipd r ((snipDisk G r hplan hscyc).face
          ((snipDisk G r hplan hscyc).edge xd))) = G.snipd r xd := by
        have e1 : G.snipd r ((snipDisk G r hplan hscyc).node
            ((snipDisk G r hplan hscyc).face ((snipDisk G r hplan hscyc).edge xd)))
            = G.node (G.snipd r ((snipDisk G r hplan hscyc).face
              ((snipDisk G r hplan hscyc).edge xd))) := rfl
        rw [← e1, (snipDisk G r hplan hscyc).edgeK xd]
      have hface : G.face (G.edge (G.snipd r xd))
          = G.snipd r ((snipDisk G r hplan hscyc).face ((snipDisk G r hplan hscyc).edge xd)) :=
        G.node.injective (by rw [G.edgeK, hnode])
      have h1 : G.pickFaceColor (G.snipd r) kd (G.snipr (G.revRing r) xr) = kd xd :=
        hpick _ _ (SameCycle.refl _ _)
      have h2 : G.pickFaceColor (G.snipd r) kd
          (G.snipr (G.revRing r) ((G.revSnipRem r hplan hplain hscyc).edge xr))
          = kd ((snipDisk G r hplan hscyc).face ((snipDisk G r hplan hscyc).edge xd)) := by
        refine hpick _ _ ?_
        rw [← hface]
        exact G.cface_face _
      rw [h1, h2, hkd.face]
      exact hkd.edge xd
    refine ⟨fun xr => G.pickFaceColor (G.snipd r) kd (G.snipr (G.revRing r) xr), ⟨?_, ?_⟩, ?_⟩
    · intro xr
      by_cases hxr : G.snipr (G.revRing r) xr ∈ G.revRing r
      · -- on the reverse ring, argue at the other end of the edge
        have hex : G.snipr (G.revRing r) ((G.revSnipRem r hplan hplain hscyc).edge xr)
            ∉ G.revRing r := by
          change G.edge (G.snipr (G.revRing r) xr) ∉ G.revRing r
          rw [mem_revRing hplain, hplain.edge_edge]
          intro hc
          have hnd := diskN_edge_ring hplan hplain hscyc hproper ((mem_revRing hplain).mp hxr)
          rw [hplain.edge_edge] at hnd
          exact hnd (diskN_of_mem hc)
        have hinv : (G.revSnipRem r hplan hplain hscyc).edge
            ((G.revSnipRem r hplan hplain hscyc).edge xr) = xr :=
          Subtype.ext (hplain.edge_edge _)
        have h := krE _ hex
        rw [hinv] at h
        exact fun hc => h hc.symm
      · exact krE xr hxr
    · intro xr
      exact (pickFaceColor_congr _ _ ((revSnip_patch hplan hplain hscyc).cface_hr xr)).symm
    · have hmaps : (G.revSniprRingRot r).map
          (fun xr => G.pickFaceColor (G.snipd r) kd (G.snipr (G.revRing r) xr))
          = (G.snipdRing r).map kd := by
        refine List.ext_getElem (by
          rw [List.length_map, List.length_map, length_revSniprRingRot, length_snipdRing]) ?_
        intro i h1 h2
        have h1' : i < (G.revSniprRingRot r).length := by rwa [List.length_map] at h1
        have h2' : i < (G.snipdRing r).length := by rwa [List.length_map] at h2
        rw [List.getElem_map, List.getElem_map]
        exact hpick _ _ (cface_getElem_borders hscyc.isCyclicChain h1' h2')
      rw [hmaps]
  · -- from the remainder of `revRing r` to the disk of `r`
    rintro ⟨kr, hkr, rfl⟩
    have hpickR : ∀ (w : D) (u : {z : D // ¬ G.DiskE (G.revRing r) z}),
        G.CFace w (G.snipr (G.revRing r) u) →
        G.pickFaceColor (G.snipr (G.revRing r)) kr w = kr u :=
      fun _ _ h => pickFaceColor_eq _ _ hkr.face hmonoR h
    have hkdface : ∀ ud : {z : D // G.DiskN r z},
        G.pickFaceColor (G.snipr (G.revRing r)) kr
            (G.snipd r ((snipDisk G r hplan hscyc).face ud))
          = G.pickFaceColor (G.snipr (G.revRing r)) kr (G.snipd r ud) :=
      fun ud => (pickFaceColor_congr _ _
        (cface_snipd hplan hscyc ((snipDisk G r hplan hscyc).cface_face ud))).symm
    -- the colour changes across every node step of the disk
    have hnodeNe : ∀ ud : {z : D // G.DiskN r z},
        G.pickFaceColor (G.snipr (G.revRing r)) kr (G.snipd r ud)
          ≠ G.pickFaceColor (G.snipr (G.revRing r)) kr
              (G.snipd r ((snipDisk G r hplan hscyc).node ud)) := by
      intro ud
      have hnN : ¬ G.DiskE (G.revRing r) (G.node (G.snipd r ud)) := by
        intro hc
        have h1 : G.DiskN (G.revRing r) (G.node (G.snipd r ud)) := hc.1
        rw [diskN_revRing hplan hplain hconn hscyc hproper] at h1
        exact h1 (diskN_node ud.2)
      set nxr : {z : D // ¬ G.DiskE (G.revRing r) z} := ⟨G.node (G.snipd r ud), hnN⟩ with hnxr
      have hA : G.pickFaceColor (G.snipr (G.revRing r)) kr
          (G.snipd r ((snipDisk G r hplan hscyc).node ud)) = kr nxr :=
        hpickR _ _ (SameCycle.refl _ _)
      have hcf : G.CFace (G.snipd r ud) (G.edge (G.node (G.snipd r ud))) := by
        have h0 := G.cface_face (G.edge (G.node (G.snipd r ud)))
        rw [G.nodeK] at h0
        exact h0.symm
      have hB : G.pickFaceColor (G.snipr (G.revRing r)) kr (G.snipd r ud)
          = kr ((G.revSnipRem r hplan hplain hscyc).edge nxr) := hpickR _ _ hcf
      rw [hA, hB]
      exact hkr.edge nxr
    refine ⟨fun ud => G.pickFaceColor (G.snipr (G.revRing r)) kr (G.snipd r ud),
      ⟨?_, hkdface⟩, ?_⟩
    · intro xd
      have h1 := hnodeNe ((snipDisk G r hplan hscyc).face ((snipDisk G r hplan hscyc).edge xd))
      rw [(snipDisk G r hplan hscyc).edgeK xd, hkdface] at h1
      exact h1
    · have hmaps : (G.snipdRing r).map
          (fun ud => G.pickFaceColor (G.snipr (G.revRing r)) kr (G.snipd r ud))
          = (G.revSniprRingRot r).map kr := by
        refine List.ext_getElem (by
          rw [List.length_map, List.length_map, length_revSniprRingRot, length_snipdRing]) ?_
        intro i h1 h2
        have h1' : i < (G.snipdRing r).length := by rwa [List.length_map] at h1
        have h2' : i < (G.revSniprRingRot r).length := by rwa [List.length_map] at h2
        rw [List.getElem_map, List.getElem_map]
        exact hpickR _ _ (cface_getElem_borders hscyc.isCyclicChain h2' h1').symm
      rw [hmaps]

/-- Kempe closure only depends on the predicate. -/
private theorem kempeClosed_congr {P Q : List Color → Prop} (h : ∀ et, P et ↔ Q et)
    (hP : KempeClosed P) : KempeClosed Q := by
  intro et het
  obtain ⟨hmap, w, hw, hw2⟩ := hP et ((h et).mpr het)
  exact ⟨fun g => (h _).mp (hmap g), w, hw, fun et' h' => (h _).mp (hw2 et' h')⟩

/-- **The ring traces of the disk of a ring of a cubic map are Kempe-closed.**
The remainder of the reverse ring is a planar plain quasicubic map with a
duplicate-free N-cycle perimeter, so its ring traces are Kempe-closed; the two
sets of traces coincide. -/
theorem ring_disk_closed (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) (hcubic : G.Cubic) :
    KempeClosed ((snipDisk G r hplan hscyc).RingTrace (G.snipdRing r)) := by
  classical
  have hcycR := isCyclicChain_sniprRing hplan (scycle_revRing hplain hscyc)
  have hstep : ∀ u : {z : D // ¬ G.DiskE (G.revRing r) z}, u ∉ G.revSniprRing r →
      ((G.revSnipRem r hplan hplain hscyc).node u : D) = G.node (u : D) := by
    intro u hu
    change G.sniprNode (G.revRing r) (u : D) = G.node (u : D)
    exact sniprNode_of_not_mem fun hc => hu (mem_sniprRing.mpr hc)
  have hclosed : ∀ u : {z : D // ¬ G.DiskE (G.revRing r) z}, u ∉ G.revSniprRing r →
      (G.revSnipRem r hplan hplain hscyc).node u ∉ G.revSniprRing r :=
    fun u hu hc => hu ((node_mem_iff_mem hcycR u).mp hc)
  have hmemrot : ∀ u : {z : D // ¬ G.DiskE (G.revRing r) z},
      u ∉ G.revSniprRingRot r → u ∉ G.revSniprRing r := by
    intro u hu hc
    exact hu (by rw [revSniprRingRot]; exact List.mem_rotate.mpr hc)
  have hgeo : (G.revSnipRem r hplan hplain hscyc).UcyclePlanarPlainQuasicubic
      (G.revSniprRingRot r) := by
    refine ⟨⟨⟨⟨fun u => Subtype.ext (hplain.edge_edge _),
      fun u hc => hplain.edge_ne (u : D) (congrArg Subtype.val hc)⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩,
      planar_revSnipRem hplan hplain hscyc⟩
    · intro u hu
      have hu0 := hmemrot u hu
      have hu1 := hclosed u hu0
      have hu2 := hclosed _ hu1
      refine Subtype.ext ?_
      rw [hstep _ hu2, hstep _ hu1, hstep _ hu0]
      exact hcubic.node_node_node (u : D)
    · intro u hu hc
      refine hcubic.node_ne (u : D) ?_
      rw [← hstep u (hmemrot u hu)]
      exact congrArg Subtype.val hc
    · rw [revSniprRingRot]
      exact isCyclicChain_rotate.mpr hcycR
    · rw [revSniprRingRot]
      exact List.nodup_rotate.mpr (nodup_sniprRing (scycle_revRing hplain hscyc))
  refine kempeClosed_congr
    (fun et => (rev_ring_cotrace hplan hplain hconn hscyc hproper et).symm) ?_
  exact @Kempe_map _ (Fintype.ofFinite _) (Classical.decEq _) _ _ hgeo

/-- **A ring trace of the disk of `r` and the reversed trace of the disk of
`revRing r` colour `G`.** -/
theorem colorable_from_ring (hplan : G.Planar) (hplain : G.Plain) (hconn : G.Connected)
    (hscyc : G.Scycle G.Rlink r) (hproper : G.ProperRing r) {et : List Color}
    (h1 : (snipDisk G r hplan hscyc).RingTrace (G.snipdRing r) et)
    (h2 : (G.revSnipDisk r hplan hplain hscyc).RingTrace (G.revSnipdRing r) et.reverse) :
    G.FourColorable := by
  refine (revSnip_patch hplan hplain hscyc).colorable_patch.mpr ⟨et.reverse, h2, ?_⟩
  rw [List.reverse_reverse]
  obtain ⟨kr, hkr, hetr⟩ := (rev_ring_cotrace hplan hplain hconn hscyc hproper et).mp h1
  refine ⟨kr, hkr, ?_⟩
  have hn : 0 < r.length := List.length_pos_iff.mpr (by rintro rfl; exact hproper)
  have hlen : ((G.revSniprRing r).map kr).length = r.length := by
    rw [List.length_map]
    have h : ((G.revSniprRing r).map (G.snipr (G.revRing r))).length = (r.map G.edge).length :=
      congrArg List.length map_revSniprRing
    rwa [List.length_map, List.length_map] at h
  rw [hetr, revSniprRingRot, List.map_rotate, trace_rotate, List.rotate_rotate,
    show r.length - 1 + 1 = r.length from by omega, ← hlen, ← length_trace, List.rotate_length]

end RevRingTrace

end Hypermap

end FourColor



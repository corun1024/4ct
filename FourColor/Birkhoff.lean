import FourColor.RevSnip
import FourColor.KempeTree
import FourColor.InitCtree
import FourColor.InitGtree
import FourColor.CfColor

/-!
# Birkhoff's lemma and the spoke ring

**Birkhoff's lemma**: a minimal counter-example to the Four Colour Theorem is
*internally five-connected* — no ring of at most five darts separates two
nontrivial parts of the map (`Hypermap.MinimalCounterExample.birkhoffRings`).
This file states the property as `Hypermap.BirkhoffRings`, proves it from four
reducibility checks closed by kernel computation, and derives the geometric
consequences the rest of the development needs, chief among them that a minimal
counter-example is **pentagonal**
(`Hypermap.MinimalCounterExample.pentagonal`).

The proof of the lemma itself glues the disk cut off by the ring to each
configuration of a small basis, appeals to minimality to colour the glued map,
and runs the trace-elimination loop of `FourColor/KempeTree.lean` on the two
sides of the ring until one of them is disjoint from a basis colouring tree.
The counting that makes the glued map smaller than `G` is the Euler formula for
quasicubic maps applied to the remainder of the cut.

The *spoke* of a dart `y` is `face (edge y)`, the dart of the neighbouring face
that `y` points at; equivalently `node⁻¹ y`.  The *spoke ring* at a dart `x` is
the list of spokes of the face of `x`, taken in reverse order, so that it is a
ring (a face-simple `Rlink` cycle) running once around the face of `x`.  In a
map with the Birkhoff property the spoke ring is moreover chordless, and its
disk is exactly the face of `x`; colouring by position around a spoke ring of at
most four darts then produces a colouring of the whole map, which is what forces
the arity to be at least five.

Every consequence is also available in a `_of_birkhoff` form taking
`Hypermap.BirkhoffRings` as an explicit hypothesis, for use by developments that
carry it around rather than rederiving it.

## Main definitions

* `Hypermap.BirkhoffRings` — the Birkhoff property: no nontrivial ring of at
  most five darts.
* `Hypermap.spoke`, `Hypermap.spokeRing` — the spoke of a dart and the spoke
  ring of a face.
* `Hypermap.Adj01` — lying in the same or in adjacent faces.
* `cpcard`, `birkhoffCheck1`, `ctreePickRev`, `doBirkhoffCheck2`,
  `birkhoffCheck2`, `BirkhoffCheck` — the reducibility checks.
* `Hypermap.RTd` — the ring traces of the disk of a ring, as a predicate that
  does not mention the ring proof.
* `FourColor.sewMatchOf` — the matching of an E-cycle with an N-cycle of the
  same length, which is the data the sewing construction needs.

## Main results

* `Hypermap.nontrivial_cycle2` — a two-dart ring that is not an edge orbit is
  nontrivial.
* `Hypermap.double_dart` — two darts in the same face whose E-links are also in
  the same face are equal.
* `Hypermap.scycle_spokeRing`, `Hypermap.diskF_spokeRing`,
  `Hypermap.fband_spokeRing`, `Hypermap.length_spokeRing` — the spoke ring is a
  ring, its disk is the face of `x` and its band is the set of darts adjacent
  to `x`.
* `Hypermap.chordless_spokeRing` — the spoke ring has no chord.
* `Hypermap.four_lt_arity`,
  `Hypermap.MinimalCounterExample.pentagonal` — a minimal counter-example is
  pentagonal.
* `Hypermap.adj11_edge`, `Hypermap.adj12_edge`, `Hypermap.fcard_adj_adj`,
  `Hypermap.fcard_adj_max` — the local adjacency structure around a hub face.
* `birkhoffCheck_one_zero`, `birkhoffCheck_two_zero`,
  `birkhoffCheck_three_zero`, `birkhoffCheck_four_one` — the four checks,
  closed by kernel computation.
* `card_cpmap` — the map of a program has `cpcard cp` darts.
* `Hypermap.exists_ring_trace_of_check1` — the geometric half of
  `Birkhoff_valid`: a basis configuration supplies a ring trace of the disk.
* `Hypermap.birkhoff_valid` — a check for ring size `n + 1` rules out
  `m`-nontrivial rings of that size.
* `Hypermap.MinimalCounterExample.birkhoffRings` — **Birkhoff's lemma**.
* `Hypermap.MinimalCounterExample.plainCubicPentagonal` — the bundled form the
  reducibility arguments consume.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/birkhoff.v` of the Coq development.
-/


namespace FourColor

/-! ### Cyclic successors in a duplicate-free list

`CyclicNext` is the relational form of `List.next`; on a duplicate-free list the
two agree, which is how chordlessness is checked. -/

section CyclicNextNodup

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- A dart of a duplicate-free list has at most one cyclic successor. -/
theorem cyclicNext_functional {l : List α} (hl : l.Nodup) {x y z : α}
    (h1 : CyclicNext l x y) (h2 : CyclicNext l x z) : y = z := by
  classical
  obtain ⟨n, t, ht, hy⟩ := h1
  obtain ⟨m, s, hs, hz⟩ := h2
  have hts : x :: t = x :: s := (rotTo_eq_of_rotate hl ht).symm.trans (rotTo_eq_of_rotate hl hs)
  injection hts with _ hts'
  rw [hy, hz, hts']

/-- In a duplicate-free list the cyclic successor is `List.next`. -/
theorem cyclicNext_iff_next {l : List α} (hl : l.Nodup) {x y : α} (hx : x ∈ l) :
    CyclicNext l x y ↔ y = l.next x hx := by
  have hnext : CyclicNext l x (l.next x hx) := by
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    subst hxi
    rw [List.next_getElem l hl i hi]
    exact cyclicNext_getElem hi _ rfl
  exact ⟨fun h => cyclicNext_functional hl h hnext, fun h => h ▸ hnext⟩

end CyclicNextNodup

namespace Hypermap

open Equiv Equiv.Perm

variable {D : Type*} {G : Hypermap D}

/-! ### Reverse steps of the three permutations

The three permutations of a hypermap compose to the identity, so each inverse is
the composite of the other two.  These are the rewriting rules that the arity
computations below run on. -/

/-- The reverse N-step is a face step out of an E-link. -/
theorem nodeInv_eq (G : Hypermap D) (y : D) : G.node⁻¹ y = G.face (G.edge y) :=
  Equiv.Perm.inv_eq_iff_eq.mpr (G.edgeK y).symm

/-- The reverse F-step is an E-step out of an N-link. -/
theorem faceInv_eq (G : Hypermap D) (y : D) : G.face⁻¹ y = G.edge (G.node y) :=
  Equiv.Perm.inv_eq_iff_eq.mpr (G.nodeK y).symm

/-- The reverse E-step is an N-step out of an F-link. -/
theorem edgeInv_eq (G : Hypermap D) (y : D) : G.edge⁻¹ y = G.node (G.face y) :=
  Equiv.Perm.inv_eq_iff_eq.mpr (G.faceK y).symm

/-- In a plain hypermap the reverse E-step is an E-step. -/
theorem Plain.edgeInv_eq (h : G.Plain) (y : D) : G.edge⁻¹ y = G.edge y :=
  Equiv.Perm.inv_eq_iff_eq.mpr (h.edge_edge y).symm

/-- In a cubic hypermap the reverse N-step is a double N-step. -/
theorem Cubic.nodeInv_eq (h : G.Cubic) (y : D) : G.node⁻¹ y = G.node (G.node y) :=
  Equiv.Perm.inv_eq_iff_eq.mpr (h.node_node_node y).symm

/-- In a cubic hypermap two reverse N-steps make one N-step. -/
theorem Cubic.nodeInv_nodeInv (h : G.Cubic) (w : D) : G.node⁻¹ (G.node⁻¹ w) = G.node w :=
  Equiv.Perm.inv_eq_iff_eq.mpr (h.nodeInv_eq w)

/-- In a bridgeless hypermap no dart lies in the face of its N-successor. -/
theorem Bridgeless.not_cface_node (h : G.Bridgeless) (z : D) : ¬ G.CFace (G.node z) z := by
  intro hc
  have h1 : G.CFace (G.edge (G.node z)) z := by
    have h2 := G.cface_face (G.edge (G.node z))
    rwa [G.nodeK] at h2
  exact h (G.node z) (hc.trans h1.symm)


/-- The E-link of an N-successor lies in the face of the dart. -/
theorem cface_edge_node (G : Hypermap D) (w : D) : G.CFace (G.edge (G.node w)) w := by
  have h := G.cface_face (G.edge (G.node w))
  rwa [G.nodeK] at h

/-- In a bridgeless hypermap the two ends of a ring link lie in distinct
faces. -/
theorem Bridgeless.not_cface_of_rlink (h : G.Bridgeless) {u v : D} (huv : G.Rlink u v) :
    ¬ G.CFace u v := fun hc => h u (hc.trans huv.symm)

/-! ### Spokes

The spoke `face (edge y)` of a dart `y` is the dart of the neighbouring face
that `y` points at.  It is the reverse N-step, so it is a bijection with inverse
`node`. -/

/-- The spoke of a dart: the dart of the adjacent face that it points at. -/
def spoke (G : Hypermap D) (y : D) : D := G.face (G.edge y)

/-- The spoke is the reverse N-step. -/
theorem spoke_eq_nodeInv (G : Hypermap D) (y : D) : G.spoke y = G.node⁻¹ y :=
  (G.nodeInv_eq y).symm

/-- The N-successor of a spoke is the dart it came from. -/
@[simp] theorem node_spoke (G : Hypermap D) (y : D) : G.node (G.spoke y) = y := G.edgeK y

/-- The spoke of an N-successor is the dart it came from. -/
@[simp] theorem spoke_node (G : Hypermap D) (y : D) : G.spoke (G.node y) = y := G.nodeK y

/-- Distinct darts have distinct spokes. -/
theorem spoke_injective (G : Hypermap D) : Function.Injective G.spoke :=
  Function.LeftInverse.injective G.node_spoke

/-- The spoke of the reverse F-step, in a plain hypermap. -/
theorem spoke_faceInv (hplain : G.Plain) (w : D) :
    G.spoke (G.face⁻¹ w) = G.face (G.node w) := by
  change G.face (G.edge (G.face⁻¹ w)) = G.face (G.node w)
  rw [G.faceInv_eq, hplain.edge_edge]

/-- Two spokes and an F-step, in a cubic hypermap. -/
theorem face_spoke_spoke (hcubic : G.Cubic) (w : D) :
    G.face (G.spoke (G.spoke w)) = G.face (G.node w) := by
  simp only [spoke_eq_nodeInv, hcubic.nodeInv_nodeInv]

/-- A dart is `Rlink`ed to the dart two F-steps past its E-link. -/
theorem rlink_face_face_edge (G : Hypermap D) (z : D) :
    G.Rlink z (G.face (G.face (G.edge z))) :=
  (G.cface_face (G.edge z)).trans (G.cface_face (G.face (G.edge z)))

/-! ### The spoke ring

The spoke ring at `x` is the list of spokes of the darts of the face of `x`,
taken in reverse order so that it runs the right way round. -/

/-- The spoke ring at `x`: the spokes of the darts of the face of `x`, in
reverse order. -/
noncomputable def spokeRing (G : Hypermap D) (x : D) : List D :=
  (orbitList G.face x).reverse.map G.spoke

/-- The spoke ring has as many darts as the face it surrounds. -/
@[simp] theorem length_spokeRing (G : Hypermap D) (x : D) :
    (G.spokeRing x).length = G.arity x := by
  simp [spokeRing, arity]

/-- The spoke ring has no repetitions. -/
theorem nodup_spokeRing (G : Hypermap D) (x : D) : (G.spokeRing x).Nodup :=
  List.Nodup.map G.spoke_injective (List.nodup_reverse.mpr (nodup_orbitList G.face x))

/-- The darts of the spoke ring, by position. -/
theorem getElem_spokeRing {x : D} {i : ℕ} (hi : i < (G.spokeRing x).length) :
    (G.spokeRing x)[i] = G.spoke ((G.face ^ (G.arity x - 1 - i)) x) := by
  simp only [spokeRing, List.getElem_map, List.getElem_reverse, orbitList, List.getElem_range,
    List.length_map, List.length_range, arity]

/-- Walking one step round the face of `x` moves one position back along the
spoke ring. -/
theorem face_pow_step (x : D) {i : ℕ} (hi : i < G.arity x) :
    G.face ((G.face ^ (G.arity x - 1 - (i + 1) % G.arity x)) x)
      = (G.face ^ (G.arity x - 1 - i)) x := by
  set n := G.arity x with hn
  rcases Nat.lt_or_ge (i + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, ← Equiv.Perm.mul_apply, ← pow_succ',
      show n - 1 - (i + 1) + 1 = n - 1 - i from by omega]
  · have hk : (i + 1) % n = 0 := by
      rw [show i + 1 = n from by omega, Nat.mod_self]
    have hx : (G.face ^ n) x = x := by
      rw [hn, arity]; exact pow_minimalPeriod G.face x
    rw [hk, show n - 1 - i = 0 from by omega, pow_zero, Equiv.Perm.one_apply,
      show n - 1 - 0 = n - 1 from by omega, ← Equiv.Perm.mul_apply, ← pow_succ',
      show n - 1 + 1 = n from by omega, hx]

section Finite

variable [Finite D]

/-! ### The Birkhoff property -/

/-- **The Birkhoff property**: no ring of at most five darts is nontrivial —
with two faces required on each side at five darts, and one on each side below.
This is the conclusion of Birkhoff's lemma for a minimal counter-example. -/
def BirkhoffRings (G : Hypermap D) : Prop :=
  ∀ r : List D, r.length ≤ 5 → G.Scycle G.Rlink r →
    ¬ G.NontrivialRing (if r.length = 5 then 1 else 0) r

/-- A ring with no darts bounds no face, so it is never nontrivial. -/
theorem not_nontrivialRing_nil (m : ℕ) : ¬ G.NontrivialRing m ([] : List D) := by
  intro h
  have h0 : G.faceCard (G.DiskF ([] : List D)) = 0 :=
    faceCard_eq_zero fun z hz => by
      obtain ⟨w, hw, -⟩ := hz.1
      simp at hw
  have h1 : m < G.faceCard (G.DiskF ([] : List D)) := h.1
  omega

omit [Finite D] in
/-- In a bridgeless map a one-dart list is never a ring. -/
theorem not_scycle_singleton (hbridge : G.Bridgeless) (x : D) :
    ¬ G.Scycle G.Rlink [x] := fun h =>
  hbridge x (isCyclicChain_singleton.mp h.1).symm

/-! ### Two-dart rings

A two-dart ring that is not an edge orbit separates the map: the N-successor of
one of its darts is strictly inside, and the N-successor of the opposite E-link
is strictly outside. -/

/-- **A two-dart ring that is not an edge orbit is nontrivial.** -/
theorem nontrivial_cycle2 (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hcubic : G.Cubic) {x y : D} (hscyc : G.Scycle G.Rlink [x, y]) (hne : G.edge x ≠ y) :
    G.NontrivialRing 0 [x, y] := by
  have hxy : G.Rlink x y := (List.isChain_cons_cons.mp hscyc.1.isChain).1
  have hin1 : G.DiskN [x, y] (G.node x) :=
    diskN_node_iff.mpr (diskN_of_mem (List.mem_cons_self ..))
  have hin2 : ¬ G.Fband [x, y] (G.node x) := by
    simp only [fband_cons, fband_nil, or_false]
    rintro (hc | hc)
    · exact hbridge.not_cface_node x hc
    · refine hbridge.not_cface_node (G.node x) ?_
      have h1 : G.CFace (G.edge x) (G.node x) := hxy.trans hc.symm
      have h2 : G.CFace (G.face (G.edge x)) (G.node x) := sameCycle_apply_left.mpr h1
      rwa [← G.nodeInv_eq, hcubic.nodeInv_eq] at h2
  set u : D := G.node (G.edge x) with hu
  have hnodeu : G.node u = G.face x := by
    rw [hu, ← hcubic.nodeInv_eq, G.nodeInv_eq, hplain.edge_edge]
  have hout1 : ¬ G.DiskN [x, y] u := by
    rw [hu, diskN_node_iff]
    intro hc
    rcases diskN_iff.mp hc with hmem | hE
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · exact hplain.edge_ne x h1
      · exact hne h1
    · exact ((diskE_edge_iff hplan hscyc).mp hE).2 (List.mem_cons_self ..)
  have hout2 : ¬ G.Fband [x, y] u := by
    simp only [fband_cons, fband_nil, or_false]
    rintro (hc | hc)
    · refine hbridge.not_cface_node u ?_
      have h1 : G.CFace x (G.node u) := by rw [hnodeu]; exact G.cface_face x
      exact (hc.trans h1).symm
    · refine hbridge u ?_
      have h1 : G.CFace (G.edge x) u := hxy.trans hc.symm
      have h2 : G.face (G.edge u) = G.edge x := by rw [hu, G.nodeK]
      have h3 : G.CFace (G.edge u) (G.edge x) := by
        have h4 := G.cface_face (G.edge u); rwa [h2] at h4
      exact (h3.trans h1).symm
  exact nontrivialRing_zero_iff.mpr ⟨⟨G.node x, hin1, hin2⟩, ⟨u, hout1, hout2⟩⟩

/-! ### Double darts

In a map with the Birkhoff property two distinct darts cannot lie in the same
face *and* have their E-links in a common face: the two-dart ring they would
form is nontrivial. -/

/-- **Two darts in a common face whose E-links share a face are equal.** -/
theorem double_dart (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hcubic : G.Cubic) (hB : G.BirkhoffRings) {x y : D} (hf : G.CFace x y)
    (he : G.CFace (G.edge x) (G.edge y)) : x = y := by
  by_contra hne
  have hyx : G.Rlink (G.edge y) x := by
    change G.CFace (G.edge (G.edge y)) x
    rw [hplain.edge_edge]
    exact hf.symm
  have hscyc : G.Scycle G.Rlink [x, G.edge y] := by
    refine ⟨isCyclicChain_cons.mpr
      ⟨List.isChain_cons_cons.mpr ⟨he, List.isChain_singleton _⟩, hyx⟩, ?_⟩
    refine simple_cons.mpr ⟨?_, simple_cons.mpr ⟨by simp, simple_nil⟩⟩
    simp only [fband_cons, fband_nil, or_false]
    intro hc
    exact hbridge y (hf.symm.trans hc)
  have hne2 : G.edge x ≠ G.edge y := fun h => hne (G.edge.injective h)
  refine hB [x, G.edge y] (by simp) hscyc ?_
  simpa using nontrivial_cycle2 hplan hplain hbridge hcubic hscyc hne2

/-! ### The spoke ring is a ring -/

/-- A dart lies on the spoke ring at `x` exactly when its N-successor lies in
the face of `x`. -/
theorem mem_spokeRing {x y : D} : y ∈ G.spokeRing x ↔ G.CFace x (G.node y) := by
  rw [spokeRing]
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := List.mem_map.mp h
    rw [List.mem_reverse] at hz
    rw [← hzy, G.node_spoke]
    exact mem_orbitList.mp hz
  · intro h
    exact List.mem_map.mpr ⟨G.node y, List.mem_reverse.mpr (mem_orbitList.mpr h), G.spoke_node y⟩

/-- The spoke of a dart of the face of `x` lies on the spoke ring at `x`. -/
theorem spoke_mem_spokeRing {x w : D} (h : G.CFace x w) : G.spoke w ∈ G.spokeRing x :=
  mem_spokeRing.mpr (by rw [G.node_spoke]; exact h)

/-- The F-successor of the reverse N-step out of a ring dart is again on the
ring. -/
theorem face_nodeInv_mem_spokeRing (hplain : G.Plain) (hcubic : G.Cubic) {x z : D}
    (hz : z ∈ G.spokeRing x) : G.face (G.node⁻¹ z) ∈ G.spokeRing x := by
  refine mem_spokeRing.mpr ?_
  have h1 : G.node (G.face (G.node⁻¹ z)) = G.edge (G.node⁻¹ z) := by
    rw [← G.edgeInv_eq, hplain.edgeInv_eq]
  have h2 : G.face (G.edge (G.node⁻¹ z)) = G.node z := by
    rw [← G.nodeInv_eq, hcubic.nodeInv_nodeInv]
  have h3 : G.CFace (G.edge (G.node⁻¹ z)) (G.node z) := by
    have h4 := G.cface_face (G.edge (G.node⁻¹ z)); rwa [h2] at h4
  rw [h1]
  exact (mem_spokeRing.mp hz).trans h3.symm

omit [Finite D] in
/-- **The spoke ring is an `Rlink` cycle.** -/
theorem isCyclicChain_spokeRing (hplain : G.Plain) (hcubic : G.Cubic) (x : D) :
    IsCyclicChain G.Rlink (G.spokeRing x) := by
  refine isCyclicChain_of_rel_getElem fun i k hi hk hik => ?_
  have hi' : i < G.arity x := by simpa using hi
  have hik' : k = (i + 1) % G.arity x := by simpa using hik
  subst hik'
  have hstep := face_pow_step (G := G) x hi'
  rw [getElem_spokeRing hi, getElem_spokeRing hk,
    show (G.face ^ (G.arity x - 1 - (i + 1) % G.arity x)) x
        = G.face⁻¹ ((G.face ^ (G.arity x - 1 - i)) x) from by rw [← hstep]; simp,
    spoke_faceInv hplain, ← face_spoke_spoke hcubic]
  exact rlink_face_face_edge G _

/-- **The spoke ring is face-simple.** -/
theorem simple_spokeRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hcubic : G.Cubic) (hB : G.BirkhoffRings) (x : D) : G.Simple (G.spokeRing x) := by
  have key : G.Simple ((orbitList G.face x).map G.spoke) := by
    refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem ?_ (nodup_orbitList G.face x))
    intro a b ha hb hab hc
    refine hab (double_dart hplan hplain hbridge hcubic hB ?_ ?_)
    · exact (mem_orbitList.mp ha).symm.trans (mem_orbitList.mp hb)
    · exact ((G.cface_face (G.edge a)).trans hc).trans (G.cface_face (G.edge b)).symm
  exact key.perm ((List.reverse_perm (orbitList G.face x)).map G.spoke).symm

/-- **The spoke ring is a ring.** -/
theorem scycle_spokeRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hcubic : G.Cubic) (hB : G.BirkhoffRings) (x : D) :
    G.Scycle G.Rlink (G.spokeRing x) :=
  ⟨isCyclicChain_spokeRing hplain hcubic x,
    simple_spokeRing hplan hplain hbridge hcubic hB x⟩

/-! ### Walking round the spoke ring -/

omit [Finite D] in
/-- The cyclic successor of a dart of the spoke ring. -/
theorem next_spokeRing [DecidableEq D] (hplain : G.Plain) (hcubic : G.Cubic) {x y : D}
    (hy : y ∈ G.spokeRing x) : (G.spokeRing x).next y hy = G.face (G.spoke y) := by
  obtain ⟨i, hi, hyi⟩ := List.getElem_of_mem hy
  subst hyi
  rw [List.next_getElem _ (G.nodup_spokeRing x) i hi]
  have hi' : i < G.arity x := by simpa using hi
  have hk : (i + 1) % (G.spokeRing x).length < (G.spokeRing x).length :=
    Nat.mod_lt _ (by omega)
  rw [getElem_spokeRing hk, getElem_spokeRing hi]
  simp only [length_spokeRing]
  rw [show (G.face ^ (G.arity x - 1 - (i + 1) % G.arity x)) x
        = G.face⁻¹ ((G.face ^ (G.arity x - 1 - i)) x) from by
      rw [← face_pow_step (G := G) x hi']; simp,
    spoke_faceInv hplain, face_spoke_spoke hcubic]

/-- The cyclic successor of a dart of the spoke ring, as a membership fact. -/
theorem face_spoke_mem_spokeRing (hplain : G.Plain) (hcubic : G.Cubic) {x y : D}
    (hy : y ∈ G.spokeRing x) : G.face (G.spoke y) ∈ G.spokeRing x := by
  refine mem_spokeRing.mpr ?_
  have h1 : G.node (G.face (G.spoke y)) = G.edge (G.spoke y) := by
    rw [← G.edgeInv_eq, hplain.edgeInv_eq]
  have h2 : G.face (G.edge (G.spoke y)) = G.node y := by
    rw [← G.nodeInv_eq, spoke_eq_nodeInv, hcubic.nodeInv_nodeInv]
  have h3 : G.CFace (G.edge (G.spoke y)) (G.node y) := by
    have h4 := G.cface_face (G.edge (G.spoke y)); rwa [h2] at h4
  rw [h1]
  exact (mem_spokeRing.mp hy).trans h3.symm

/-- The cyclic predecessor of a dart of the spoke ring. -/
theorem prev_spokeRing [DecidableEq D] (hplain : G.Plain) (hcubic : G.Cubic) {x y : D}
    (hy : y ∈ G.spokeRing x) :
    (G.spokeRing x).prev y hy = G.node (G.edge (G.node y)) := by
  set z : D := G.node (G.edge (G.node y)) with hz
  have hnz : G.node z = G.face (G.node y) := by
    rw [hz, ← hcubic.nodeInv_eq, G.nodeInv_eq, hplain.edge_edge]
  have hzr : z ∈ G.spokeRing x := by
    refine mem_spokeRing.mpr ?_
    rw [hnz]
    exact (mem_spokeRing.mp hy).trans (G.cface_face (G.node y))
  have hnext : G.face (G.spoke z) = y := by
    rw [spoke_eq_nodeInv, hz]
    have h1 : G.node⁻¹ (G.node (G.edge (G.node y))) = G.edge (G.node y) := by simp
    rw [h1, ← G.faceInv_eq]
    simp
  have h2 := List.prev_next (G.spokeRing x) (G.nodup_spokeRing x) z hzr
  have h3 : (G.spokeRing x).next z hzr = y := by
    rw [next_spokeRing hplain hcubic hzr, hnext]
  have key : ∀ (a b : D) (ha : a ∈ G.spokeRing x) (hb : b ∈ G.spokeRing x), a = b →
      (G.spokeRing x).prev a ha = (G.spokeRing x).prev b hb := by
    rintro a b ha hb rfl
    rfl
  exact (key y ((G.spokeRing x).next z hzr) hy (List.next_mem _ _ _) h3.symm).trans h2

/-! ### The band and the disk of the spoke ring -/

/-- The face band of the spoke ring at `x` is the set of darts adjacent to
`x`. -/
theorem fband_spokeRing {x y : D} : G.Fband (G.spokeRing x) y ↔ G.Adj x y := by
  constructor
  · rintro ⟨z, hz, hyz⟩
    refine ⟨G.node z, mem_spokeRing.mp hz, ?_⟩
    have h1 : G.CFace (G.edge (G.node z)) z := by
      have h2 := G.cface_face (G.edge (G.node z)); rwa [G.nodeK] at h2
    exact h1.trans hyz.symm
  · rintro ⟨z, hxz, hzy⟩
    exact ⟨G.spoke z, spoke_mem_spokeRing hxz, hzy.symm.trans (G.cface_face (G.edge z))⟩

omit [Finite D] in
/-- A contour path leaving a dart of a ring stays in its face band. -/
private theorem fband_of_dpath {r : List D} {w y : D} (hw : w ∈ r)
    (hpath : Relation.ReflTransGen (G.DLink r) w y) : G.Fband r y := by
  rcases Relation.ReflTransGen.cases_head hpath with h | ⟨z, hlink, -⟩
  · exact h ▸ fband_of_mem hw
  · exact absurd hw hlink.1

/-- A contour path out of the face of `x` that avoids the band of the spoke ring
stays in the face of `x`. -/
private theorem cface_of_dpath {x : D} : ∀ {w y : D},
    Relation.ReflTransGen (G.DLink (G.spokeRing x)) w y → G.CFace x w →
      ¬ G.Fband (G.spokeRing x) y → G.CFace x y := by
  intro w y hpath
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h _ => h
  | head hlink hrest ih =>
      intro hxa hy
      rcases hlink.2 with hcl | hcl
      · exact absurd (fband_of_dpath (mem_spokeRing.mpr (hcl ▸ hxa)) hrest) hy
      · exact ih (hcl ▸ hxa.trans (G.cface_face _)) hy

/-- **The face-closed disk of the spoke ring at `x` is the face of `x`.** -/
theorem diskF_spokeRing (hplain : G.Plain) (hbridge : G.Bridgeless) (hcubic : G.Cubic)
    {x y : D} : G.DiskF (G.spokeRing x) y ↔ G.CFace x y := by
  constructor
  · rintro ⟨⟨z, hz, hconn⟩, hband⟩
    have hpath : Relation.ReflTransGen (G.DLink (G.spokeRing x)) (G.node⁻¹ z) y := hconn
    have hfz : G.face (G.node⁻¹ z) ∈ G.spokeRing x :=
      face_nodeInv_mem_spokeRing hplain hcubic hz
    rcases Relation.ReflTransGen.cases_head hpath with h | ⟨z1, hlink, hrest⟩
    · refine absurd (h ▸ ?_) hband
      exact (⟨G.face (G.node⁻¹ z), hfz, G.cface_face (G.node⁻¹ z)⟩ :
        G.Fband (G.spokeRing x) (G.node⁻¹ z))
    · rcases hlink.2 with hcl | hcl
      · have hz1 : z1 = G.node z := by
          have h1 : z1 = G.node⁻¹ (G.node⁻¹ z) := by rw [hcl]; simp
          rw [h1, hcubic.nodeInv_nodeInv]
        refine cface_of_dpath hrest ?_ hband
        rw [hz1]
        exact mem_spokeRing.mp hz
      · exact absurd (fband_of_dpath (hcl ▸ hfz) hrest) hband
  · intro hxy
    refine ⟨?_, ?_⟩
    · have h1 : G.DiskN (G.spokeRing x) (G.node (G.spoke y)) :=
        diskN_node_iff.mpr (diskN_of_mem (spoke_mem_spokeRing hxy))
      rwa [G.node_spoke] at h1
    · rintro ⟨z, hz, hyz⟩
      exact hbridge.not_cface_node z ((mem_spokeRing.mp hz).symm.trans (hxy.trans hyz))

/-! ### The spoke ring has no chord

A chord of the spoke ring would give a three-dart ring separating the N-link of
one endpoint from the N-link of the other, which the Birkhoff property
forbids. -/

/-- Darts of the spoke ring in a common face are equal. -/
theorem eq_of_cface_spokeRing (hplan : G.Planar) (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hcubic : G.Cubic) (hB : G.BirkhoffRings) {x u v : D} (hu : u ∈ G.spokeRing x)
    (hv : v ∈ G.spokeRing x) (huv : G.CFace u v) : u = v :=
  (simple_spokeRing hplan hplain hbridge hcubic hB x).eq_of_cface hu hv huv

/-- Proofs of membership do not matter for `List.next`. -/
private theorem next_congr {α : Type*} [DecidableEq α] (l : List α) {u v : α}
    (hu : u ∈ l) (hv : v ∈ l) (h : u = v) : l.next u hu = l.next v hv := by
  subst h; rfl

/-- **The spoke ring has no chord.** -/
theorem chordless_spokeRing (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hB : G.BirkhoffRings) (x : D) :
    G.Chordless (G.spokeRing x) := by
  classical
  intro y1 hy1 y2 hy2 hadj
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hnc1, hnc2⟩ := hcon
  obtain ⟨z, hz1, hz2⟩ := hadj
  have hnodup := G.nodup_spokeRing x
  have hx1 : G.CFace x (G.node y1) := mem_spokeRing.mp hy1
  have hx2 : G.CFace x (G.node y2) := mem_spokeRing.mp hy2
  set a : D := G.node y2 with ha
  set b : D := G.edge z with hb
  set c : D := G.edge (G.node y1) with hc
  have hby2 : G.CFace b y2 := hz2
  have hcy1 : G.CFace c y1 := by
    have h := G.cface_face c
    rwa [show G.face c = y1 from G.nodeK y1] at h
  have hay2 : G.CFace (G.edge a) y2 := by
    have h := G.cface_face (G.edge a)
    rwa [show G.face (G.edge a) = y2 from G.nodeK y2] at h
  have hec : G.edge c = G.node y1 := hplain.edge_edge _
  have heb : G.edge b = z := hplain.edge_edge _
  -- the three-dart ring
  set q : List D := [a, b, c] with hq
  have hnab : ¬ G.CFace a b := fun h => hbridge.not_cface_node y2 (h.trans hby2)
  have hnac : ¬ G.CFace a c := by
    intro h
    exact hbridge.not_cface_node y1 ((hx2.symm.trans hx1).symm.trans (h.trans hcy1))
  have hnbc : ¬ G.CFace b c := fun h => hbridge z (((h.trans hcy1).trans hz1).symm)
  have hscycq : G.Scycle G.Rlink q := by
    refine ⟨isCyclicChain_cons.mpr ⟨List.isChain_cons_cons.mpr ⟨hay2.trans hby2.symm, ?_⟩, ?_⟩, ?_⟩
    · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton c⟩
      change G.CFace (G.edge b) c
      rw [heb]
      exact hz1.symm.trans hcy1.symm
    · change G.CFace (G.edge c) a
      rw [hec]
      exact hx1.symm.trans hx2
    · refine simple_cons.mpr ⟨?_, simple_cons.mpr ⟨?_, simple_cons.mpr ⟨by simp, simple_nil⟩⟩⟩
      · simp only [fband_cons, fband_nil, or_false]
        rintro (h | h)
        · exact hnab h
        · exact hnac h
      · simp only [fband_cons, fband_nil, or_false]
        exact hnbc
  have hqmem_a : a ∈ q := List.mem_cons_self ..
  have hqmem_b : b ∈ q := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hqmem_c : c ∈ q := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- the inside witness: the cyclic predecessor of `y1`
  set t : D := G.node c with ht
  have htprev : (G.spokeRing x).prev y1 hy1 = t := prev_spokeRing hplain hcubic hy1
  have htmem : t ∈ G.spokeRing x := htprev ▸ List.prev_mem _ _ _
  have htin : G.DiskF q t := by
    refine ⟨diskN_node_iff.mpr (diskN_of_mem hqmem_c), ?_⟩
    simp only [hq, fband_cons, fband_nil, or_false]
    rintro (h | h | h)
    · refine hbridge.not_cface_node t ?_
      exact (h.trans ((mem_spokeRing.mp htmem).symm.trans hx2).symm).symm
    · have hty2 : t = y2 :=
        eq_of_cface_spokeRing hplan hplain hbridge hcubic hB htmem hy2 (h.trans hby2)
      refine hnc2 ((cyclicNext_iff_next hnodup hy2).mpr ?_)
      have h1 := List.next_prev (G.spokeRing x) hnodup y1 hy1
      rw [← next_congr (G.spokeRing x) hy2 (List.prev_mem _ _ _)
        (hty2.symm.trans htprev.symm)] at h1
      exact h1.symm
    · exact hbridge.not_cface_node c h
  -- the outside witness: the spoke of `y1`
  set s : D := G.node (G.node y1) with hs
  have hsspoke : G.spoke y1 = s := by rw [spoke_eq_nodeInv, hcubic.nodeInv_eq, hs]
  have hsout : G.DiskFC q s := by
    refine ⟨?_, ?_⟩
    · rw [hs, diskN_node_iff, ← hec]
      exact diskN_edge_ring hplan hplain hscycq
        (G.properRing_of_two_lt_length (by simp [hq])) hqmem_c
    · simp only [hq, fband_cons, fband_nil, or_false]
      rintro (h | h | h)
      · refine hbridge.not_cface_node (G.node y1) ?_
        exact h.trans (hx2.symm.trans hx1)
      · have hfs : G.face s = (G.spokeRing x).next y1 hy1 := by
          rw [next_spokeRing hplain hcubic hy1, hsspoke]
        have h1 : G.CFace (G.face s) y2 :=
          ((G.cface_face s).symm.trans h).trans hby2
        rw [hfs] at h1
        refine hnc1 ((cyclicNext_iff_next hnodup hy1).mpr ?_)
        exact (eq_of_cface_spokeRing hplan hplain hbridge hcubic hB
          (List.next_mem _ _ _) hy2 h1).symm
      · refine hbridge y1 ?_
        have h1 : G.CFace s y1 := h.trans hcy1
        have h2 : G.face (G.edge y1) = s := by
          rw [hs, ← hcubic.nodeInv_eq, G.nodeInv_eq]
        have h3 : G.CFace (G.edge y1) s := by
          have h4 := G.cface_face (G.edge y1); rwa [h2] at h4
        exact (h3.trans h1).symm
  refine hB q (by simp [hq]) hscycq ?_
  have hlen : q.length = 3 := by simp [hq]
  rw [hlen]
  simpa using nontrivialRing_zero_iff.mpr ⟨⟨t, htin⟩, ⟨s, hsout⟩⟩

/-! ### The minimal arity is five

If the spoke ring at `x` had at most four darts then either it would separate
the map — contradicting the Birkhoff property — or its face band would cover
everything outside the face of `x`, and colouring the face of `x` apart from the
at most four faces around it would colour the whole map. -/

/-- The colour given to a dart by its position on a ring of at most four
darts. -/
private def ringColor (n i : ℕ) : Color :=
  if i = 2 ∧ n = 3 then Color.c3 else if i = 0 ∨ i = 2 then Color.c1 else Color.c2

/-- Cyclically consecutive positions on a ring of two, three or four darts get
different colours. -/
private theorem ringColor_ne {n i j : ℕ} (hn2 : 2 ≤ n) (hn4 : n ≤ 4) (hi : i < n) (hj : j < n)
    (h : j = (i + 1) % n ∨ i = (j + 1) % n) : ringColor n j ≠ ringColor n i := by
  have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hn with rfl | rfl | rfl <;> rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;> simp_all [ringColor]

/-- **A minimal counter-example with the Birkhoff property has no face of fewer
than five darts.** -/
theorem four_lt_arity (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) (x : D) : 4 < G.arity x := by
  classical
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  by_contra hle
  push Not at hle
  have hscyc := scycle_spokeRing hplan hplain hbridge hcubic hB x
  have hnodup := G.nodup_spokeRing x
  have hlen : (G.spokeRing x).length = G.arity x := length_spokeRing G x
  have h5 : ¬ ((G.spokeRing x).length = 5) := by rw [hlen]; omega
  have hifs : (if (G.spokeRing x).length = 5 then (1 : ℕ) else 0) = 0 := by
    rw [hlen]
    split
    · omega
    · rfl
  by_cases hex : ∃ y, G.DiskFC (G.spokeRing x) y
  · obtain ⟨y, hy⟩ := hex
    refine hB (G.spokeRing x) (by rw [hlen]; omega) hscyc ?_
    rw [hifs]
    exact nontrivialRing_zero_iff.mpr
      ⟨⟨x, (diskF_spokeRing hplain hbridge hcubic).mpr (Equiv.Perm.SameCycle.refl _ _)⟩, ⟨y, hy⟩⟩
  · push Not at hex
    have hband : ∀ w : D, ¬ G.CFace x w → G.Fband (G.spokeRing x) w := by
      intro w hw
      rcases fband_or_diskF_or_diskFC w with h | h | h
      · exact h
      · exact absurd ((diskF_spokeRing hplain hbridge hcubic).mp h) hw
      · exact absurd h (hex w)
    have hpos : 0 < (G.spokeRing x).length := by
      rw [hlen]
      simpa [arity] using minimalPeriod_pos G.face x
    have hne1 : (G.spokeRing x).length ≠ 1 := by
      intro hL
      obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp hL
      exact not_scycle_singleton hbridge w (hw ▸ hscyc)
    have hn2 : 2 ≤ (G.spokeRing x).length := by omega
    have hn4 : (G.spokeRing x).length ≤ 4 := by rw [hlen]; omega
    refine hmin.noncolorable ⟨fun w => if G.CFace x w then Color.c0 else
      ringColor (G.spokeRing x).length ((G.spokeRing x).idxOf (G.fproj (G.spokeRing x) w)),
      ?_, ?_⟩
    · intro w
      by_cases hxw : G.CFace x w
      · have hxew : ¬ G.CFace x (G.edge w) := fun hc => hbridge w (hxw.symm.trans hc)
        simp only [hxw, hxew, reduceIte, ringColor]
        split_ifs <;> simp
      · by_cases hxew : G.CFace x (G.edge w)
        · simp only [hxw, hxew, reduceIte, ringColor]
          split_ifs <;> simp
        · simp only [hxw, hxew, reduceIte]
          set z1 : D := G.fproj (G.spokeRing x) w with hz1def
          set z2 : D := G.fproj (G.spokeRing x) (G.edge w) with hz2def
          have hz1 : z1 ∈ G.spokeRing x := G.fproj_mem (hband w hxw)
          have hz2 : z2 ∈ G.spokeRing x := G.fproj_mem (hband (G.edge w) hxew)
          have hw1 : G.CFace w z1 := G.cface_fproj w
          have hw2 : G.CFace (G.edge w) z2 := G.cface_fproj (G.edge w)
          have hne12 : z1 ≠ z2 := by
            intro h
            refine hbridge w ?_
            rw [← h] at hw2
            exact hw1.trans hw2.symm
          have hadj : G.Adj z1 z2 := ⟨w, hw1.symm, hw2⟩
          have hch := chordless_spokeRing hplan hplain hbridge hcubic hB x z1 hz1 z2 hz2 hadj
          have hi1 : (G.spokeRing x).idxOf z1 < (G.spokeRing x).length :=
            List.idxOf_lt_length_iff.mpr hz1
          have hi2 : (G.spokeRing x).idxOf z2 < (G.spokeRing x).length :=
            List.idxOf_lt_length_iff.mpr hz2
          have hstep : (G.spokeRing x).idxOf z2
                = ((G.spokeRing x).idxOf z1 + 1) % (G.spokeRing x).length ∨
              (G.spokeRing x).idxOf z1
                = ((G.spokeRing x).idxOf z2 + 1) % (G.spokeRing x).length := by
            rcases hch with h | h | h
            · exact absurd h.symm hne12
            · refine Or.inl ?_
              have h1 := (cyclicNext_iff_next hnodup hz1).mp h
              rw [List.next_eq_getElem hz1] at h1
              rw [h1, hnodup.idxOf_getElem]
            · refine Or.inr ?_
              have h1 := (cyclicNext_iff_next hnodup hz2).mp h
              rw [List.next_eq_getElem hz2] at h1
              rw [h1, hnodup.idxOf_getElem]
          exact ringColor_ne hn2 hn4 hi1 hi2 hstep
    · intro w
      have h1 : G.CFace x (G.face w) = G.CFace x w := propext sameCycle_apply_right
      have h2 : G.fproj (G.spokeRing x) (G.face w) = G.fproj (G.spokeRing x) w :=
        G.fproj_congr (G.cface_face w).symm
      simp only [h1, h2]

/-- **A minimal counter-example with the Birkhoff property is pentagonal.** -/
theorem MinimalCounterExample.pentagonal_of_birkhoff
    (hmin : G.MinimalCounterExample) (hB : G.BirkhoffRings) : G.Pentagonal :=
  fun x => four_lt_arity hmin hB x

/-! ### Adjacency across the spoke ring -/

/-- `y` and `z` lie in the same face or in adjacent faces. -/
def Adj01 (G : Hypermap D) (y z : D) : Prop := G.CFace y z ∨ G.Adj y z

/-- **An E-link with both ends adjacent to `x` has one end on the spoke ring.**
-/
theorem adj11_edge (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hB : G.BirkhoffRings) {x y : D}
    (h1 : G.Adj x y) (h2 : G.Adj x (G.edge y)) :
    y ∈ G.spokeRing x ∨ G.edge y ∈ G.spokeRing x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hy, hey⟩ := hcon
  obtain ⟨z, hz, hyz⟩ := fband_spokeRing.mpr h1
  obtain ⟨t, ht, hety⟩ := fband_spokeRing.mpr h2
  have hscyc := scycle_spokeRing hplan hplain hbridge hcubic hB x
  have hnodup := G.nodup_spokeRing x
  have hadj : G.Adj z t := ⟨y, hyz.symm, hety⟩
  rcases chordless_spokeRing hplan hplain hbridge hcubic hB x z hz t ht hadj with h | h | h
  · rw [h] at hety
    exact hbridge y (hyz.trans hety.symm)
  · have hnext : t = (G.spokeRing x).next z hz := (cyclicNext_iff_next hnodup hz).mp h
    have hrl : G.Rlink z ((G.spokeRing x).next z hz) := rel_next hscyc.1 hnodup hz
    rw [← hnext] at hrl
    have hyzeq : y = z :=
      double_dart hplan hplain hbridge hcubic hB hyz (hety.trans hrl.symm)
    exact hy (by rw [hyzeq]; exact hz)
  · have hnext : z = (G.spokeRing x).next t ht := (cyclicNext_iff_next hnodup ht).mp h
    have hrl : G.Rlink t ((G.spokeRing x).next t ht) := rel_next hscyc.1 hnodup ht
    rw [← hnext] at hrl
    have hee : G.CFace (G.edge (G.edge y)) (G.edge t) := by
      rw [hplain.edge_edge]
      exact hyz.trans hrl.symm
    have heyeq : G.edge y = t :=
      double_dart hplan hplain hbridge hcubic hB hety hee
    exact hey (by rw [heyeq]; exact ht)

/-- **Two darts adjacent to `x` whose link crosses an E-link out of `x`'s
neighbourhood are themselves close.**  This is the reference's `adj12_edge`. -/
theorem adj12_edge (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hB : G.BirkhoffRings) {x y z : D}
    (h1 : G.Adj x y) (h2 : G.Adj x z) (h3 : G.Adj z (G.edge y)) :
    G.Adj01 z y ∨ G.Adj01 x (G.edge y) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hzy, hxey⟩ := hcon
  rw [Adj01, not_or] at hzy hxey
  obtain ⟨hzFy, hzAy⟩ := hzy
  obtain ⟨hxFey, hxAey⟩ := hxey
  obtain ⟨y1, hy1, hyy1⟩ := fband_spokeRing.mpr h1
  obtain ⟨z1, hz1, hzz1⟩ := fband_spokeRing.mpr h2
  obtain ⟨x1, hzx1, hx1ey⟩ := h3
  have hxy1 : G.CFace x (G.node y1) := mem_spokeRing.mp hy1
  have hxz1 : G.CFace x (G.node z1) := mem_spokeRing.mp hz1
  have hz1Fy : ¬ G.CFace z1 y := fun hc => hzFy (hzz1.trans hc)
  have hz1x1 : G.CFace z1 x1 := hzz1.symm.trans hzx1
  have hz1Ay : ¬ G.Adj z1 y := fun hc => hzAy ((adj_congr_left hzz1 y).mpr hc)
  have hx1 : G.CFace (G.edge y) (G.edge x1) := hx1ey.symm
  set a : D := y with hadef
  set b : D := G.edge x1 with hbdef
  set c : D := G.edge (G.node z1) with hcdef
  set d : D := G.node y1 with hddef
  have hcz1 : G.CFace c z1 := G.cface_edge_node z1
  have hdy1 : G.CFace (G.edge d) y1 := G.cface_edge_node y1
  have heb : G.edge b = x1 := hplain.edge_edge _
  have hec : G.edge c = G.node z1 := hplain.edge_edge _
  set q : List D := [a, b, c, d] with hq
  have hRab : G.Rlink a b := hx1
  have hRbc : G.Rlink b c := by
    change G.CFace (G.edge b) c
    rw [heb]
    exact hz1x1.symm.trans hcz1.symm
  have hRcd : G.Rlink c d := by
    change G.CFace (G.edge c) d
    rw [hec]
    exact hxz1.symm.trans hxy1
  have hRda : G.Rlink d a := hdy1.trans hyy1.symm
  have hnac : ¬ G.CFace a c := fun hc => hz1Fy ((hc.trans hcz1).symm)
  have hnbd : ¬ G.CFace b d := by
    intro hc
    exact hxFey ((hxy1.trans hc.symm).trans hx1.symm)
  have hscycq : G.Scycle G.Rlink q := by
    refine ⟨isCyclicChain_cons.mpr ⟨List.isChain_cons_cons.mpr ⟨hRab,
      List.isChain_cons_cons.mpr ⟨hRbc, List.isChain_cons_cons.mpr ⟨hRcd,
        List.isChain_singleton d⟩⟩⟩, hRda⟩, ?_⟩
    refine simple_cons.mpr ⟨?_, simple_cons.mpr ⟨?_,
      simple_cons.mpr ⟨?_, simple_cons.mpr ⟨by simp, simple_nil⟩⟩⟩⟩
    · simp only [fband_cons, fband_nil, or_false]
      rintro (h | h | h)
      · exact hbridge.not_cface_of_rlink hRab h
      · exact hnac h
      · exact hbridge.not_cface_of_rlink hRda h.symm
    · simp only [fband_cons, fband_nil, or_false]
      rintro (h | h)
      · exact hbridge.not_cface_of_rlink hRbc h
      · exact hnbd h
    · simp only [fband_cons, fband_nil, or_false]
      exact hbridge.not_cface_of_rlink hRcd
  have hqa : a ∈ q := List.mem_cons_self ..
  have hqb : b ∈ q := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hqc : c ∈ q :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hqd : d ∈ q :=
    List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  -- the inside witness
  set s : D := G.node (G.node y1) with hsdef
  have hsface : s = G.face (G.edge y1) := hcubic.node_node y1
  have hsE : G.CFace (G.edge y1) s := by rw [hsface]; exact G.cface_face (G.edge y1)
  have hAxs : G.Adj x s := (adj_congr_left hxy1 s).mpr (hplain.adj_symm (G.adj_node (G.node y1)))
  have hsin : G.DiskF q s := by
    refine ⟨diskN_node_iff.mpr (diskN_of_mem hqd), ?_⟩
    simp only [hq, fband_cons, fband_nil, or_false]
    rintro (h | h | h | h)
    · exact hbridge y1 (((hsE.trans h).trans hyy1).symm)
    · exact not_cface_of_not_adj hxAey hAxs (hx1.trans h.symm)
    · refine not_cface_of_not_adj (fun hc => hz1Ay (hplain.adj_symm hc))
        ((adj_congr_left hyy1 (G.edge y1)).mpr (G.adj_edge y1)) ?_
      exact ((hsE.trans h).trans hcz1).symm
    · exact hbridge.not_cface_node (G.node y1) h
  -- the outside witness
  set u : D := G.node (G.node z1) with hudef
  have huface : u = G.face (G.edge z1) := hcubic.node_node z1
  have hAxu : G.Adj x u := (adj_congr_left hxz1 u).mpr (hplain.adj_symm (G.adj_node (G.node z1)))
  have huz1 : G.CFace (G.edge z1) u := by rw [huface]; exact G.cface_face (G.edge z1)
  have hsout : G.DiskFC q u := by
    refine ⟨?_, ?_⟩
    · rw [hudef, diskN_node_iff, ← hec]
      exact diskN_edge_ring hplan hplain hscycq
        (G.properRing_of_two_lt_length (by simp [hq])) hqc
    · simp only [hq, fband_cons, fband_nil, or_false]
      rintro (h | h | h | h)
      · exact not_cface_of_not_adj hz1Ay (G.adj_edge z1) ((huz1.trans h).symm)
      · exact not_cface_of_not_adj hxAey hAxu (hx1.trans h.symm)
      · exact hbridge z1 ((huz1.trans (h.trans hcz1)).symm)
      · refine hbridge u ?_
        have hun : G.CFace (G.edge u) (G.node z1) := G.cface_edge_node (G.node z1)
        exact ((hun.trans (hxz1.symm.trans (hxy1.trans h.symm))).symm)
  refine hB q (by simp [hq]) hscycq ?_
  have hlen : q.length = 4 := by simp [hq]
  rw [hlen]
  simpa using nontrivialRing_zero_iff.mpr ⟨⟨s, hsin⟩, ⟨u, hsout⟩⟩

/-! ### Counting the faces adjacent to two adjacent faces -/

/-- Proofs of membership do not matter for `List.prev`. -/
private theorem prev_congr {α : Type*} [DecidableEq α] (l : List α) {u v : α}
    (hu : u ∈ l) (hv : v ∈ l) (h : u = v) : l.prev u hu = l.prev v hv := by
  subst h; rfl

/-- The two cyclic neighbours of a dart of a duplicate-free cycle of more than
two darts are distinct. -/
private theorem next_ne_prev {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (h3 : 2 < l.length) {w : α} (hw : w ∈ l) : l.prev w hw ≠ l.next w hw := by
  intro heq
  have hi : l.idxOf w < l.length := List.idxOf_lt_length_iff.mpr hw
  have hmem : l.next w hw ∈ l := List.next_mem _ _ _
  have hstep : l.next (l.next w hw) hmem = w :=
    (next_congr l hmem (List.prev_mem l w hw) heq.symm).trans (List.next_prev l hl w hw)
  have hidxv : l.idxOf (l.next w hw) = (l.idxOf w + 1) % l.length := by
    rw [List.next_eq_getElem hw, hl.idxOf_getElem]
  have hw2 : l.next (l.next w hw) hmem
      = l[((l.idxOf w + 1) % l.length + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
    rw [List.next_eq_getElem hmem, hidxv]
  have hwi : l[l.idxOf w] = w := List.getElem_idxOf hi
  have hkey : ((l.idxOf w + 1) % l.length + 1) % l.length = l.idxOf w := by
    exact (hl.getElem_inj_iff (hi := Nat.mod_lt _ (by omega)) (hj := hi)).mp
      ((hw2.symm.trans hstep).trans hwi.symm)
  rcases Nat.lt_or_ge (l.idxOf w + 1) l.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hkey
    rcases Nat.lt_or_ge (l.idxOf w + 1 + 1) l.length with hlt2 | hge2
    · rw [Nat.mod_eq_of_lt hlt2] at hkey; omega
    · rw [show l.idxOf w + 1 + 1 = l.length from by omega, Nat.mod_self] at hkey; omega
  · rw [show l.idxOf w + 1 = l.length from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (show 1 < l.length by omega)] at hkey
    omega

omit [Finite D] in
/-- A set of darts that meets exactly two faces. -/
private theorem faceCard_eq_two {A : D → Prop} {z₁ z₂ : D} (h₁ : A z₁) (h₂ : A z₂)
    (hne : ¬ G.CFace z₁ z₂) (hsub : ∀ w, A w → G.CFace w z₁ ∨ G.CFace w z₂) :
    G.faceCard A = 2 := by
  classical
  have himg : (Quotient.mk (SameCycle.setoid G.face) '' {w | A w})
      = {Quotient.mk (SameCycle.setoid G.face) z₁,
         Quotient.mk (SameCycle.setoid G.face) z₂} := by
    ext c
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hsub w hw with h | h
      · exact Or.inl (Quotient.sound h)
      · exact Or.inr (Quotient.sound h)
    · rintro (rfl | rfl)
      · exact ⟨z₁, h₁, rfl⟩
      · exact ⟨z₂, h₂, rfl⟩
  rw [faceCard, himg, Set.ncard_pair (fun hc => hne (Quotient.exact hc))]

/-- **A face adjacent to the hub meets exactly two faces adjacent to both.**
This is the reference's `fcard_adj_adj`. -/
theorem fcard_adj_adj (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) {x y : D} (hxy : G.Adj x y) :
    G.faceCard (fun w => G.Adj y w ∧ G.Adj x w) = 2 := by
  classical
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  have hscyc := scycle_spokeRing hplan hplain hbridge hcubic hB x
  have hnodup := G.nodup_spokeRing x
  have hlen3 : 2 < (G.spokeRing x).length := by
    have h4 := four_lt_arity hmin hB x
    rw [length_spokeRing]
    omega
  obtain ⟨y1, hy1, hyy1⟩ := fband_spokeRing.mpr hxy
  set z₁ : D := (G.spokeRing x).prev y1 hy1 with hz1def
  set z₂ : D := (G.spokeRing x).next y1 hy1 with hz2def
  have hz1 : z₁ ∈ G.spokeRing x := List.prev_mem _ _ _
  have hz2 : z₂ ∈ G.spokeRing x := List.next_mem _ _ _
  have hxA : ∀ w ∈ G.spokeRing x, G.Adj x w := fun w hw =>
    (adj_congr_left (mem_spokeRing.mp hw) w).mpr (G.adj_node w)
  have hyA1 : G.Adj y z₁ :=
    (adj_congr_left hyy1 z₁).mpr (hplain.adj_symm (rel_prev hscyc.1 hnodup hy1).adj)
  have hyA2 : G.Adj y z₂ :=
    (adj_congr_left hyy1 z₂).mpr (rel_next hscyc.1 hnodup hy1).adj
  have hne : ¬ G.CFace z₁ z₂ := fun hc =>
    next_ne_prev hnodup hlen3 hy1
      (eq_of_cface_spokeRing hplan hplain hbridge hcubic hB hz1 hz2 hc)
  refine faceCard_eq_two ⟨hyA1, hxA _ hz1⟩ ⟨hyA2, hxA _ hz2⟩ hne ?_
  rintro t ⟨hyt, hxt⟩
  obtain ⟨t1, ht1, htt1⟩ := fband_spokeRing.mpr hxt
  have hadj : G.Adj y1 t1 :=
    (adj_congr_right htt1 y1).mp ((adj_congr_left hyy1 t).mp hyt)
  rcases chordless_spokeRing hplan hplain hbridge hcubic hB x y1 hy1 t1 ht1 hadj with
    h | h | h
  · exact absurd (hyy1.trans (h ▸ htt1).symm) (hbridge.not_cface_of_adj hyt)
  · have ht : t1 = z₂ := (cyclicNext_iff_next hnodup hy1).mp h
    exact Or.inr (by rw [← ht]; exact htt1)
  · have hy : y1 = (G.spokeRing x).next t1 ht1 := (cyclicNext_iff_next hnodup ht1).mp h
    have ht : z₁ = t1 := by
      rw [hz1def, prev_congr (G.spokeRing x) hy1 (List.next_mem _ _ _) hy]
      exact List.prev_next (G.spokeRing x) hnodup t1 ht1
    exact Or.inl (by rw [ht]; exact htt1)

/-! ### At most two faces meet two given faces

A face not in the face of the hub meets at most two of the faces around the hub:
three of them would be pairwise adjacent, and three pairwise consecutive darts
on a ring of at least five darts would have to close up into a three-cycle. -/

/-- The position of a cyclic successor. -/
private theorem idxOf_next {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) {w : α}
    (hw : w ∈ l) : l.idxOf (l.next w hw) = (l.idxOf w + 1) % l.length := by
  rw [List.next_eq_getElem hw, hl.idxOf_getElem]

/-- Three successive cyclic steps never return to the start on a cycle of more
than three positions. -/
private theorem three_step {i n : ℕ} (hn : 3 < n) (hi : i < n)
    (h : (((i + 1) % n + 1) % n + 1) % n = i) : False := by
  rcases Nat.lt_or_ge (i + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    rcases Nat.lt_or_ge (i + 1 + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h
      rcases Nat.lt_or_ge (i + 1 + 1 + 1) n with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at h; omega
      · rw [show i + 1 + 1 + 1 = n from by omega, Nat.mod_self] at h; omega
    · rw [show i + 1 + 1 = n from by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (show 1 < n by omega)] at h
      omega
  · rw [show i + 1 = n from by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (show 1 < n by omega),
      Nat.mod_eq_of_lt (show 1 + 1 < n by omega)] at h
    omega

/-- Three darts of a duplicate-free cycle of more than three darts cannot follow
each other round. -/
private theorem next_cube_ne {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (hn : 3 < l.length) {a b c : α} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (h1 : l.next a ha = b) (h2 : l.next b hb = c) (h3 : l.next c hc = a) : False := by
  have e1 : l.idxOf b = (l.idxOf a + 1) % l.length := by rw [← h1]; exact idxOf_next hl ha
  have e2 : l.idxOf c = (l.idxOf b + 1) % l.length := by rw [← h2]; exact idxOf_next hl hb
  have e3 : l.idxOf a = (l.idxOf c + 1) % l.length := by rw [← h3]; exact idxOf_next hl hc
  rw [e1] at e2
  rw [e2] at e3
  exact three_step hn (List.idxOf_lt_length_iff.mpr ha) e3.symm

/-- A set meeting more than two faces has three darts in pairwise distinct
faces. -/
private theorem exists_three_of_two_lt_faceCard {A : D → Prop} (h : 2 < G.faceCard A) :
    ∃ z₁ z₂ z₃, A z₁ ∧ A z₂ ∧ A z₃ ∧ ¬ G.CFace z₁ z₂ ∧ ¬ G.CFace z₁ z₃ ∧
      ¬ G.CFace z₂ z₃ := by
  classical
  rw [faceCard, Set.two_lt_ncard (Set.toFinite _)] at h
  obtain ⟨-, ⟨z₁, hz₁, rfl⟩, -, ⟨z₂, hz₂, rfl⟩, -, ⟨z₃, hz₃, rfl⟩, h12, h13, h23⟩ := h
  exact ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, fun hc => h12 (Quotient.sound hc),
    fun hc => h13 (Quotient.sound hc), fun hc => h23 (Quotient.sound hc)⟩

/-- Two faces both adjacent to the hub and to a further face, and not in the
face of the hub, are adjacent to each other. -/
private theorem cross_adj (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) {x y : D} (hxy01 : ¬ G.Adj01 x y) {z t : D}
    (hzt : ¬ G.CFace z t) (hxz : G.Adj x z) (hxt : G.Adj x t) (hyz : G.Adj y z)
    (hyt : G.Adj y t) : G.Adj z t := by
  have hplain := hmin.plain
  obtain ⟨u, hyu, hut⟩ := hyt
  have hxeu : G.Adj x (G.edge u) := (adj_congr_right hut x).mpr hxt
  have hzeeu : G.Adj z (G.edge (G.edge u)) := by
    rw [hplain.edge_edge]
    exact hplain.adj_symm ((adj_congr_left hyu z).mp hyz)
  rcases adj12_edge hmin.planar hplain hmin.bridgeless hmin.cubic hB hxeu hxz hzeeu with h | h
  · rcases h with h | h
    · exact absurd (h.trans hut) hzt
    · exact (adj_congr_right hut z).mp h
  · rw [hplain.edge_edge] at h
    rcases h with h | h
    · exact absurd (Or.inl (h.trans hyu.symm) : G.Adj01 x y) hxy01
    · exact absurd (Or.inr ((adj_congr_right hyu x).mpr h) : G.Adj01 x y) hxy01

/-- Two adjacent darts of the spoke ring follow each other, and their cyclic
successors differ. -/
private theorem ring_pair [DecidableEq D] (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) {x u v : D} (huv : G.Adj u v) (hu : u ∈ G.spokeRing x)
    (hv : v ∈ G.spokeRing x) :
    (G.spokeRing x).next u hu ≠ (G.spokeRing x).next v hv ∧
      ((G.spokeRing x).next u hu = v ∨ (G.spokeRing x).next v hv = u) := by
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  have hnodup := G.nodup_spokeRing x
  have huvne : u ≠ v := by
    intro h
    subst h
    exact hbridge.not_cface_of_adj huv (Equiv.Perm.SameCycle.refl _ _)
  constructor
  · intro h
    refine huvne ?_
    have h1 := List.prev_next (G.spokeRing x) hnodup u hu
    have h2 := List.prev_next (G.spokeRing x) hnodup v hv
    rw [← h1, ← h2, prev_congr (G.spokeRing x) (List.next_mem _ _ _) (List.next_mem _ _ _) h]
  · rcases chordless_spokeRing hplan hplain hbridge hcubic hB x u hu v hv huv with h | h | h
    · exact absurd h.symm huvne
    · exact Or.inl ((cyclicNext_iff_next hnodup hu).mp h).symm
    · exact Or.inr ((cyclicNext_iff_next hnodup hv).mp h).symm

/-- **A face outside the face of the hub meets at most two faces adjacent to
both it and the hub.**  This is the reference's `fcard_adj_max`. -/
theorem fcard_adj_max (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) {x y : D} (hxy : ¬ G.CFace x y) :
    G.faceCard (fun w => G.Adj y w ∧ G.Adj x w) ≤ 2 := by
  classical
  by_cases hadj : G.Adj x y
  · exact le_of_eq (fcard_adj_adj hmin hB hadj)
  have hxy01 : ¬ G.Adj01 x y := fun h => h.elim hxy hadj
  by_contra hgt
  push Not at hgt
  obtain ⟨z1, z2, z3, ⟨hy1, hx1⟩, ⟨hy2, hx2⟩, ⟨hy3, hx3⟩, n12, n13, n23⟩ :=
    exists_three_of_two_lt_faceCard hgt
  have a12 := cross_adj hmin hB hxy01 n12 hx1 hx2 hy1 hy2
  have a13 := cross_adj hmin hB hxy01 n13 hx1 hx3 hy1 hy3
  have a23 := cross_adj hmin hB hxy01 n23 hx2 hx3 hy2 hy3
  obtain ⟨t1, ht1, hc1⟩ := fband_spokeRing.mpr hx1
  obtain ⟨t2, ht2, hc2⟩ := fband_spokeRing.mpr hx2
  obtain ⟨t3, ht3, hc3⟩ := fband_spokeRing.mpr hx3
  have hA12 : G.Adj t1 t2 := (adj_congr_right hc2 t1).mp ((adj_congr_left hc1 z2).mp a12)
  have hA13 : G.Adj t1 t3 := (adj_congr_right hc3 t1).mp ((adj_congr_left hc1 z3).mp a13)
  have hA23 : G.Adj t2 t3 := (adj_congr_right hc3 t2).mp ((adj_congr_left hc2 z3).mp a23)
  have hne12 : t1 ≠ t2 := fun h =>
    n12 ((show G.CFace z1 t2 by rw [← h]; exact hc1).trans hc2.symm)
  have hne23 : t2 ≠ t3 := fun h =>
    n23 ((show G.CFace z2 t3 by rw [← h]; exact hc2).trans hc3.symm)
  obtain ⟨hn12, hd12⟩ := ring_pair hmin hB hA12 ht1 ht2
  obtain ⟨hn13, hd13⟩ := ring_pair hmin hB hA13 ht1 ht3
  obtain ⟨hn23, hd23⟩ := ring_pair hmin hB hA23 ht2 ht3
  have hnodup := G.nodup_spokeRing x
  have hlen : 3 < (G.spokeRing x).length := by
    have h4 := four_lt_arity hmin hB x
    rw [length_spokeRing]
    omega
  rcases hd12 with e12 | e21
  · have e31 : (G.spokeRing x).next t3 ht3 = t1 := by
      rcases hd13 with e13 | e31
      · exact absurd (e12.symm.trans e13) hne23
      · exact e31
    have e23 : (G.spokeRing x).next t2 ht2 = t3 := by
      rcases hd23 with e23 | e32
      · exact e23
      · exact absurd (e31.symm.trans e32) hne12
    exact next_cube_ne hnodup hlen ht1 ht2 ht3 e12 e23 e31
  · rcases hd13 with e13 | e31
    · have e32 : (G.spokeRing x).next t3 ht3 = t2 := by
        rcases hd23 with e23 | e32
        · exact absurd (e13.trans e23.symm) hn12
        · exact e32
      exact next_cube_ne hnodup hlen ht1 ht3 ht2 e13 e32 e21
    · exact absurd (e21.trans e31.symm) hn23

/-! ### Reducing the Birkhoff property to the interesting ring sizes -/

/-- To establish the Birkhoff property it is enough to treat rings of two to
five darts: a ring with no darts bounds no face, and a one-dart ring would be a
bridge. -/
theorem birkhoffRings_of_two_le (hbridge : G.Bridgeless)
    (h : ∀ r : List D, 2 ≤ r.length → r.length ≤ 5 → G.Scycle G.Rlink r →
      ¬ G.NontrivialRing (if r.length = 5 then 1 else 0) r) : G.BirkhoffRings := by
  intro r hlen hscyc
  rcases Nat.lt_or_ge r.length 2 with hlt | hge
  · match r with
    | [] => exact not_nontrivialRing_nil _
    | [w] => exact absurd hscyc (not_scycle_singleton hbridge w)
    | _ :: _ :: _ => simp at hlt
  · exact h r hge hlen hscyc

/-- **A minimal counter-example with the Birkhoff property is plain, cubic and
pentagonal**, which is what the reducibility arguments consume. -/
theorem MinimalCounterExample.plainCubicPentagonal_of_birkhoff
    (hmin : G.MinimalCounterExample) (hB : G.BirkhoffRings) : G.PlainCubicPentagonal :=
  ⟨⟨hmin.plain, hmin.cubic⟩, hmin.pentagonal_of_birkhoff hB⟩

end Finite

end Hypermap

/-! ### The Birkhoff reducibility checks

The computational half of Birkhoff's lemma.  A *Birkhoff check* for ring size
`h + 1` and kernel size `m` is a finite amount of evidence that every ring of
`h + 1` darts with more than `m` faces on each side is reducible: a basis of
small cubic configuration programs (condition `birkhoffCheck1`) together with an
iteration count for the trace-elimination loop (condition `birkhoffCheck2`).

The loop alternates between the two sides of the ring.  At each round it picks a
trace that is still available on both sides — `ctreePickRev` — restricts the
corresponding colouring tree by it through `kempeTreeClosure`, and recurses;
it succeeds when one of the two colouring trees becomes disjoint from one of the
basis trees. -/

section BirkhoffCheck

/-- The number of darts of `cpmap cp`. -/
def cpcard : CProg → ℕ
  | [] => 2
  | .R _ :: cp => cpcard cp
  | .R' :: cp => cpcard cp
  | .A :: cp => cpcard cp
  | .U :: cp => cpcard cp + 2
  | .K :: cp => cpcard cp + 2
  | .Y :: cp => cpcard cp + 4
  | .H :: cp => cpcard cp + 6

/-- Whether a construction program uses only the steps that preserve
cubicity. -/
def cubicProgB : CProg → Bool
  | [] => true
  | .R _ :: cp => cubicProgB cp
  | .U :: cp => cubicProgB cp
  | .Y :: cp => cubicProgB cp
  | .H :: cp => cubicProgB cp
  | _ => false

/-- Cubicity of a program, one step at a time. -/
private theorem cubicProg_cons {s : CpStep} {cp : CProg} :
    CubicProg (s :: cp) ↔ s.IsCubic ∧ CubicProg cp := by
  simp only [CubicProg, List.mem_cons, forall_eq_or_imp]

/-- `cubicProgB` decides `CubicProg`. -/
theorem cubicProgB_iff {cp : CProg} : cubicProgB cp = true ↔ CubicProg cp := by
  induction cp with
  | nil => simp [cubicProgB, CubicProg]
  | cons s cp ih =>
    rw [cubicProg_cons, ← ih]
    cases s <;> simp [cubicProgB, CpStep.IsCubic]

/-- The basis condition: `cp` is a cubic program whose map has too few darts to
be a counter-example and whose ring has `h + 1` darts. -/
def birkhoffCheck1 (h m : ℕ) (cp : CProg) : Bool :=
  cubicProgB cp && decide (cpcard cp + 1 < 6 * m + 4 * h) && decide (cprsize cp = h + 1)

/-- The recursion of `ctreePickRev`: descend `t` while accumulating the trace
`e :: et` and the running sum `e`, and stop at the first leaf whose trace is
also in `t'`. -/
def ctreePickRevRec (t' : Ctree) : Ctree → List Color → Color → List Color
  | .leaf _, et, e => if Ctree.mem t' (evenize ((e :: et).dropLast)) then e :: et else []
  | .node t₁ t₂ t₃, et, e =>
      match ctreePickRevRec t' t₁ (Color.c1 :: et) (e + Color.c1) with
      | e' :: et' => e' :: et'
      | [] =>
        match ctreePickRevRec t' t₂ (Color.c2 :: et) (e + Color.c2) with
        | e' :: et' => e' :: et'
        | [] => ctreePickRevRec t' t₃ (Color.c3 :: et) (e + Color.c3)
  | .empty, _, _ => []

/-- A complete trace colouring whose even partial trace lies in `t'` and whose
reversed partial trace lies in `t`; the empty list if there is none. -/
def ctreePickRev (t' t : Ctree) : List Color := ctreePickRevRec t' t [] Color.c0

/-- One round of the elimination loop: restrict `ctu` by the trace `et` and
check that the resulting gram tree is exhausted and that either the basis test
or the continuation succeeds. -/
def doBirkhoffCheck2 (h : ℕ) (checkBasis : Ctree → Bool) (et : List Color)
    (ctu : Ctree) (gtu : Gtree) (chk : Ctree → Gtree → Bool) : Bool :=
  if (0 : Color) ∈ et then false
  else
    let r := kempeTreeClosure (h - 1) h ctu (Ctree.ofTrace (evenize et)) gtu
    r.2.1.isEmpty && (checkBasis r.1 || chk r.1 r.2.2)

/-- The elimination loop, alternating between the two sides of the ring. -/
def birkhoffCheck2 (h : ℕ) (checkBasis : Ctree → Bool) :
    ℕ → Ctree → Gtree → Ctree → Gtree → Bool
  | 0, _, _, _, _ => false
  | n + 1, ctu1, gtu1, ctu2, gtu2 =>
      match ctreePickRev ctu1 ctu2 with
      | [] => false
      | e :: et =>
          doBirkhoffCheck2 h checkBasis ((e :: et).dropLast) ctu1 gtu1
              (fun c g => birkhoffCheck2 h checkBasis n ctu2 gtu2 c g) &&
          doBirkhoffCheck2 h checkBasis et.reverse ctu2 gtu2
              (fun c g => birkhoffCheck2 h checkBasis n ctu1 gtu1 c g)

/-- **The Birkhoff check** for ring size `h + 1` and kernel size `m`: a basis of
cubic configuration programs, all passing `birkhoffCheck1`, and an iteration
count for which the elimination loop succeeds. -/
def BirkhoffCheck (h m : ℕ) : Prop :=
  ∃ (niter : ℕ) (cps : List CProg),
    cps.all (birkhoffCheck1 h m) = true ∧
    birkhoffCheck2 h (fun t => (cps.map cpcolor).any (Ctree.disjoint t)) niter
      (initTree h) (gtreeInitTree h) (initTree h) (gtreeInitTree h) = true

/-- The trace picked out of a pair of colouring trees sums to zero. -/
private theorem sum_ctreePickRevRec (t' : Ctree) : ∀ (t : Ctree) (et : List Color) (e : Color),
    e + et.sum = 0 → (ctreePickRevRec t' t et e).sum = 0 := by
  intro t
  induction t with
  | empty => intro et e _; rfl
  | leaf lf _ =>
    intro et e he
    rw [ctreePickRevRec]
    split
    · rw [List.sum_cons]; exact he
    · rfl
  | node t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro et e he
    have hstep : ∀ c : Color, (e + c) + (c :: et).sum = 0 := by
      intro c
      rw [List.sum_cons, ← add_assoc, add_assoc e c c, Color.add_self, add_zero]
      exact he
    rw [ctreePickRevRec]
    cases h₁ : ctreePickRevRec t' t₁ (Color.c1 :: et) (e + Color.c1) with
    | cons a l =>
      have := ih₁ (Color.c1 :: et) (e + Color.c1) (hstep Color.c1)
      rw [h₁] at this
      simpa using this
    | nil =>
      simp only []
      cases h₂ : ctreePickRevRec t' t₂ (Color.c2 :: et) (e + Color.c2) with
      | cons a l =>
        have := ih₂ (Color.c2 :: et) (e + Color.c2) (hstep Color.c2)
        rw [h₂] at this
        simpa using this
      | nil =>
        simp only []
        exact ih₃ (Color.c3 :: et) (e + Color.c3) (hstep Color.c3)

/-- **The trace picked by `ctreePickRev` sums to zero.** -/
theorem sum_ctreePickRev (t' t : Ctree) : (ctreePickRev t' t).sum = 0 :=
  sum_ctreePickRevRec t' t [] Color.c0 rfl

/-- The trace picked out of a proper tree is either empty or as long as the
tree is deep. -/
private theorem length_ctreePickRevRec (t' : Ctree) : ∀ (d : ℕ) (t : Ctree),
    Ctree.Proper d t → ∀ (et : List Color) (e : Color),
      ctreePickRevRec t' t et e = [] ∨
        (ctreePickRevRec t' t et e).length = et.length + d + 1 := by
  intro d
  induction d with
  | zero =>
    intro t hp et e
    match t with
    | .empty => exact Or.inl rfl
    | .leaf lf =>
      rw [ctreePickRevRec]
      split
      · exact Or.inr (by simp)
      · exact Or.inl rfl
    | .node _ _ _ => exact absurd hp (by simp [Ctree.Proper])
  | succ d ih =>
    intro t hp et e
    match t with
    | .empty => exact Or.inl rfl
    | .leaf lf => exact absurd hp (by simp [Ctree.Proper])
    | .node t₁ t₂ t₃ =>
      obtain ⟨-, hp₁, hp₂, hp₃⟩ := hp
      rw [ctreePickRevRec]
      cases h₁ : ctreePickRevRec t' t₁ (Color.c1 :: et) (e + Color.c1) with
      | cons a l =>
        have := ih t₁ hp₁ (Color.c1 :: et) (e + Color.c1)
        rw [h₁] at this
        refine Or.inr ?_
        rcases this with h | h
        · exact absurd h (by simp)
        · simp only [List.length_cons] at h ⊢
          omega
      | nil =>
        simp only []
        cases h₂ : ctreePickRevRec t' t₂ (Color.c2 :: et) (e + Color.c2) with
        | cons a l =>
          have := ih t₂ hp₂ (Color.c2 :: et) (e + Color.c2)
          rw [h₂] at this
          refine Or.inr ?_
          rcases this with h | h
          · exact absurd h (by simp)
          · simp only [List.length_cons] at h ⊢
            omega
        | nil =>
          simp only []
          have := ih t₃ hp₃ (Color.c3 :: et) (e + Color.c3)
          rcases this with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            simp only [List.length_cons] at h ⊢
            omega

/-- **The trace picked by `ctreePickRev` is either empty or a full trace.** -/
theorem length_ctreePickRev {d : ℕ} {t : Ctree} (hp : Ctree.Proper d t) (t' : Ctree) :
    ctreePickRev t' t = [] ∨ (ctreePickRev t' t).length = d + 1 := by
  have h := length_ctreePickRevRec t' d t hp [] Color.c0
  rw [ctreePickRev]
  simpa using h

/-- The Birkhoff check for two-dart rings. -/
theorem birkhoffCheck_one_zero : BirkhoffCheck 1 0 :=
  ⟨1, [[]], by decide +kernel, by decide +kernel⟩

/-- The Birkhoff check for three-dart rings. -/
theorem birkhoffCheck_two_zero : BirkhoffCheck 2 0 :=
  ⟨1, [[CpStep.Y]], by decide +kernel, by decide +kernel⟩

/-- The Birkhoff check for four-dart rings. -/
theorem birkhoffCheck_three_zero : BirkhoffCheck 3 0 :=
  ⟨4, [[CpStep.U], [CpStep.R 1, CpStep.U]], by decide +kernel, by decide +kernel⟩

/-- The Birkhoff check for five-dart rings. -/
theorem birkhoffCheck_four_one : BirkhoffCheck 4 1 :=
  ⟨10, [[CpStep.U, CpStep.Y], [CpStep.R 1, CpStep.U, CpStep.Y],
        [CpStep.R 2, CpStep.U, CpStep.Y], [CpStep.R 3, CpStep.U, CpStep.Y],
        [CpStep.R 4, CpStep.U, CpStep.Y],
        [CpStep.H, CpStep.R 4, CpStep.Y, CpStep.Y, CpStep.Y]],
    by decide +kernel, by decide +kernel⟩

/-- **The map of a program has `cpcard cp` darts.** -/
theorem card_cpmap : ∀ cp : CProg, Nat.card (cpmap cp).Dart = cpcard cp := by
  intro cp
  induction cp with
  | nil => simp [cpcard, cpmap, PointedMap.cpmap0]
  | cons s cp ih =>
    cases s with
    | R n => exact ih
    | R' => exact ih
    | A => exact ih
    | U =>
      change Nat.card (EcpDart (cpmap cp).Dart) = cpcard (.U :: cp)
      rw [EcpDart.card_eq, ih]
      rfl
    | K =>
      change Nat.card (EcpDart (cpmap cp).Dart) = cpcard (.K :: cp)
      rw [EcpDart.card_eq, ih]
      rfl
    | Y =>
      change Nat.card (EcpDart (EcpDart (cpmap cp).Dart)) = cpcard (.Y :: cp)
      rw [EcpDart.card_eq, EcpDart.card_eq, ih]
      rfl
    | H =>
      change Nat.card (EcpDart (EcpDart (EcpDart (cpmap cp).Dart))) = cpcard (.H :: cp)
      rw [EcpDart.card_eq, EcpDart.card_eq, EcpDart.card_eq, ih]
      rfl

end BirkhoffCheck

/-! ### Matching two cycles by position

Sewing two maps along a border needs the matching as data.  Two duplicate-free
cyclic chains of the same length are matched by position; the matching is then
automatically a morphism of the two link relations. -/

section MatchIdx

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The map sending the `i`-th dart of `l` to the `i`-th dart of `l'`. -/
private def matchIdx (l : List α) (l' : List β) (y₀ : β) (x : α) : β :=
  l'.getD (l.idxOf x) y₀

omit [DecidableEq β] in
/-- The matching reads off the dart at the same position. -/
private theorem matchIdx_getElem {l : List α} {l' : List β} {y₀ : β} (hl : l.Nodup)
    {i : ℕ} (hi : i < l.length) (hi' : i < l'.length) :
    matchIdx l l' y₀ l[i] = l'[i] := by
  rw [matchIdx, hl.idxOf_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  rfl

omit [DecidableEq β] in
/-- The matching maps one list into the other. -/
private theorem matchIdx_mem {l : List α} {l' : List β} {y₀ : β} (hl : l.Nodup)
    (hlen : l.length = l'.length) {x : α} (hx : x ∈ l) : matchIdx l l' y₀ x ∈ l' := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  subst hxi
  rw [matchIdx_getElem hl hi (by omega)]
  exact List.getElem_mem _

/-- The two matchings are inverse to each other. -/
private theorem matchIdx_matchIdx {l : List α} {l' : List β} {x₀ : α} {y₀ : β}
    (hl : l.Nodup) (hl' : l'.Nodup) (hlen : l.length = l'.length) {x : α} (hx : x ∈ l) :
    matchIdx l' l x₀ (matchIdx l l' y₀ x) = x := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  subst hxi
  rw [matchIdx_getElem hl hi (by omega), matchIdx_getElem hl' (by omega) hi]

omit [DecidableEq α] in
/-- Mapping one list by the matching gives the other list back. -/
private theorem map_matchIdx {l : List α} {l' : List β} {x₀ : α}
    (hl' : l'.Nodup) (hlen : l.length = l'.length) :
    l'.map (matchIdx l' l x₀) = l := by
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have hi' : i < l'.length := by simpa using h1
  rw [List.getElem_map, matchIdx_getElem hl' hi' (by omega)]

omit [DecidableEq β] in
/-- The matching of two cyclic chains is a morphism of their link maps. -/
private theorem matchIdx_step {l : List α} {l' : List β} {y₀ : β} {f : α → α} {g : β → β}
    (hl : l.Nodup) (hlen : l.length = l'.length)
    (hcl : IsCyclicChain (fun u v => v = f u) l)
    (hcl' : IsCyclicChain (fun u v => v = g u) l') {x : α} (hx : x ∈ l) :
    matchIdx l l' y₀ (f x) = g (matchIdx l l' y₀ x) := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  subst hxi
  have hL : l'.length = l.length := hlen.symm
  have hk : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  have hstep : l[(i + 1) % l.length] = f l[i] := Hypermap.rel_getElem_succ hcl hi hk rfl
  have hstep' : l'[(i + 1) % l.length]'(by omega) = g (l'[i]'(by omega)) :=
    Hypermap.rel_getElem_succ hcl' (l := l') (i := i) (k := (i + 1) % l.length)
      (by omega) (by omega) (by rw [hL])
  rw [← hstep, matchIdx_getElem hl hk (by omega), matchIdx_getElem hl hi (by omega)]
  exact hstep'

omit [DecidableEq α] in
/-- A duplicate-free cycle of a permutation is closed under it, both ways. -/
private theorem mem_iff_of_isCyclicChain [Finite α] {f : Equiv.Perm α} {l : List α}
    (hcyc : IsCyclicChain (fun u v => v = f u) l) (x : α) :
    f x ∈ l ↔ x ∈ l := by
  classical
  have hclosed : ∀ y ∈ l, f y ∈ l := fun y hy => mem_of_isCyclicChain hcyc hy
  have hsub : l.toFinset.image f ⊆ l.toFinset := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact List.mem_toFinset.mpr (hclosed y (List.mem_toFinset.mp hy))
  have hcard : l.toFinset.card ≤ (l.toFinset.image f).card := by
    rw [Finset.card_image_of_injective _ f.injective]
  have heq : l.toFinset.image f = l.toFinset := Finset.eq_of_subset_of_card_le hsub hcard
  constructor
  · intro h
    have h1 : f x ∈ l.toFinset.image f := by rw [heq]; exact List.mem_toFinset.mpr h
    obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp h1
    rw [f.injective hfy] at hy
    exact List.mem_toFinset.mp hy
  · exact hclosed x

end MatchIdx

section SewMatchOf

variable {Dd Dr : Type*} [Finite Dd] [Finite Dr] [DecidableEq Dd] [DecidableEq Dr]
variable {Gd : Hypermap Dd} {Gr : Hypermap Dr}

/-- **The matching of an E-cycle of the disk with an N-cycle of the remainder**,
by position along the reversed disk ring. -/
private noncomputable def sewMatchOf (bd : List Dd) (br : List Dr) (x₀ : Dd) (y₀ : Dr)
    (hbdcyc : IsCyclicChain (fun u v => v = Gd.edge u) bd) (hbdn : bd.Nodup)
    (hbrcyc : IsCyclicChain (fun u v => v = Gr.node u) br) (hbrn : br.Nodup)
    (hlen : bd.length = br.length) : SewMatch Gd Gr bd br where
  toRest := matchIdx bd.reverse br y₀
  toDisk := matchIdx br bd.reverse x₀
  mem_edge x := mem_iff_of_isCyclicChain hbdcyc x
  mem_node y := mem_iff_of_isCyclicChain hbrcyc y
  toRest_mem x hx :=
    matchIdx_mem (List.nodup_reverse.mpr hbdn) (by simpa using hlen)
      (List.mem_reverse.mpr hx)
  toDisk_mem y hy := by
    have h := matchIdx_mem (l := br) (l' := bd.reverse) (y₀ := x₀) hbrn
      (by simpa using hlen.symm) hy
    exact List.mem_reverse.mp h
  toDisk_toRest x hx :=
    matchIdx_matchIdx (List.nodup_reverse.mpr hbdn) hbrn (by simpa using hlen)
      (List.mem_reverse.mpr hx)
  toRest_toDisk y hy :=
    matchIdx_matchIdx hbrn (List.nodup_reverse.mpr hbdn) (by simpa using hlen.symm) hy
  node_toRest x hx := by
    have hcd : IsCyclicChain (fun u v => v = Gd.node (Gd.face u)) bd.reverse := by
      refine IsCyclicChain.congr ?_ hbdcyc.reverse
      rintro u v (h : u = Gd.edge v)
      rw [h, Gd.edgeK]
    exact (matchIdx_step (l := bd.reverse) (l' := br) (y₀ := y₀)
      (List.nodup_reverse.mpr hbdn) (by simpa using hlen) hcd hbrcyc
      (List.mem_reverse.mpr hx)).symm

/-- The sewing matcher sends the remainder ring onto the reversed disk ring. -/
private theorem map_toDisk_sewMatchOf (bd : List Dd) (br : List Dr) (x₀ : Dd) (y₀ : Dr)
    (hbdcyc : IsCyclicChain (fun u v => v = Gd.edge u) bd) (hbdn : bd.Nodup)
    (hbrcyc : IsCyclicChain (fun u v => v = Gr.node u) br) (hbrn : br.Nodup)
    (hlen : bd.length = br.length) :
    br.map (sewMatchOf bd br x₀ y₀ hbdcyc hbdn hbrcyc hbrn hlen).toDisk = bd.reverse :=
  map_matchIdx hbrn (by simpa using hlen)

end SewMatchOf

namespace Hypermap

open Equiv Equiv.Perm

/-! ### Counting the faces of the remainder map

The remainder of the cut along `r` has one face for every face of `G` that
meets the complement of the disk interior; in particular it has at least one
face for every dart of `r` and one for every face strictly outside the ring. -/

section FaceCount

variable {D : Type*} [Finite D] [DecidableEq D] {G : Hypermap D} {r : List D}

omit [DecidableEq D] in
open scoped Classical in
/-- Face counts are monotone. -/
private theorem faceCard_mono {A B : D → Prop} (h : ∀ x, A x → B x) :
    G.faceCard A ≤ G.faceCard B :=
  Set.ncard_le_ncard (Set.image_mono fun _ hx => h _ hx) (Set.toFinite _)

omit [DecidableEq D] in
open scoped Classical in
/-- Two sets of darts meeting no common face split the face count. -/
private theorem faceCard_union_eq {A B : D → Prop}
    (hdisj : ∀ x y, A x → B y → ¬ G.CFace x y) :
    G.faceCard (fun x => A x ∨ B x) = G.faceCard A + G.faceCard B := by
  have himg : (Quotient.mk (SameCycle.setoid G.face) '' {x | A x ∨ B x})
      = (Quotient.mk (SameCycle.setoid G.face) '' {x | A x})
        ∪ (Quotient.mk (SameCycle.setoid G.face) '' {x | B x}) := by
    ext q
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, Or.inl hx, rfl⟩
      · exact ⟨x, Or.inr hx, rfl⟩
  have hd : Disjoint (Quotient.mk (SameCycle.setoid G.face) '' {x | A x})
      (Quotient.mk (SameCycle.setoid G.face) '' {x | B x}) := by
    rw [Set.disjoint_left]
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hq⟩
    exact hdisj x y hx hy (Quotient.exact hq).symm
  rw [faceCard, faceCard, faceCard, himg,
    Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]

omit [Finite D] [DecidableEq D] in
open scoped Classical in
/-- A face-simple list meets exactly as many faces as it has darts. -/
private theorem faceCard_mem_eq_length (hsimple : G.Simple r) :
    G.faceCard (fun x => x ∈ r) = r.length := by
  have himg : (Quotient.mk (SameCycle.setoid G.face) '' {x | x ∈ r})
      = ↑((r.map (Quotient.mk (SameCycle.setoid G.face))).toFinset) := by
    ext q
    simp [eq_comm]
  rw [faceCard, himg, Set.ncard_coe_finset, hsimple.card_faces]

/-- **The faces of the remainder map** are exactly the faces of `G` that meet
the complement of the disk interior. -/
private theorem cycleCount_face_snipRem (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r) :
    cycleCount (snipRem G r hplan hscyc).face = G.faceCard (fun x => ¬ G.DiskE r x) := by
  classical
  set Gr := snipRem G r hplan hscyc with hGr
  have P := snip_patch hplan hscyc
  have hwd : ∀ u v : {x : D // ¬ G.DiskE r x}, Gr.CFace u v →
      Quotient.mk (SameCycle.setoid G.face) (u : D)
        = Quotient.mk (SameCycle.setoid G.face) (v : D) :=
    fun u v h => Quotient.sound ((P.cface_hr_iff u v).mp h)
  set F : Quotient (SameCycle.setoid Gr.face) → Quotient (SameCycle.setoid G.face) :=
    Quotient.lift (fun u => Quotient.mk (SameCycle.setoid G.face) (u : D)) hwd with hF
  have hinj : Function.Injective F := by
    intro a b
    refine Quotient.inductionOn₂ a b fun u v h => Quotient.sound ?_
    exact (P.cface_hr_iff u v).mpr (Quotient.exact h)
  have hrange : Set.range F
      = Quotient.mk (SameCycle.setoid G.face) '' {x : D | ¬ G.DiskE r x} := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      exact Quotient.inductionOn a fun u => ⟨(u : D), u.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Quotient.mk (SameCycle.setoid Gr.face) ⟨x, hx⟩, rfl⟩
  rw [cycleCount, faceCard, ← hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj,
    Set.ncard_univ]

/-- **A lower bound on the number of faces of the remainder map**: one for each
dart of the ring, and one for each face strictly outside it. -/
private theorem le_cycleCount_face_snipRem (hplan : G.Planar) (hscyc : G.Scycle G.Rlink r)
    {m : ℕ} (hnt : G.NontrivialRing m r) :
    r.length + m + 1 ≤ cycleCount (snipRem G r hplan hscyc).face := by
  classical
  rw [cycleCount_face_snipRem]
  have hsub : G.faceCard (fun x => x ∈ r ∨ G.DiskFC r x)
      ≤ G.faceCard (fun x => ¬ G.DiskE r x) := by
    refine faceCard_mono fun x hx => ?_
    rcases hx with hx | hx
    · exact fun hc => hc.2 hx
    · exact fun hc => hx.1 hc.1
  have hsplit : G.faceCard (fun x => x ∈ r ∨ G.DiskFC r x)
      = G.faceCard (fun x => x ∈ r) + G.faceCard (G.DiskFC r) := by
    refine faceCard_union_eq fun x y hx hy hc => ?_
    exact hy.2 ⟨x, hx, hc.symm⟩
  rw [hsplit, faceCard_mem_eq_length hscyc.simple] at hsub
  have := hnt.2
  omega

end FaceCount

/-! ### Birkhoff's lemma from the checks

`Birkhoff_valid` turns a reducibility check for ring size `n + 1` into the
absence of `m`-nontrivial rings of that size in a minimal counter-example.  Its
geometric half glues the disk of the ring to a basis configuration and appeals
to minimality; its combinatorial half runs the trace-elimination loop. -/

section BirkhoffValid

variable {D : Type*} [Finite D] [DecidableEq D] {G : Hypermap D}

/-- Composing a colouring with a colour permutation gives a colouring. -/
theorem Coloring.map_edgePerm {E : Type*} {H : Hypermap E} {k : E → Color} (g : EdgePerm)
    (h : H.Coloring k) : H.Coloring (fun x => g (k x)) :=
  ⟨fun x hc => h.edge x (g.apply_injective hc), fun x => by rw [h.face]⟩

/-- Ring traces are closed under colour permutations. -/
theorem RingTrace.map_edgePerm {E : Type*} {H : Hypermap E} {rr : List E} {et : List Color}
    (g : EdgePerm) (h : H.RingTrace rr et) : H.RingTrace rr (et.map g) := by
  obtain ⟨k, hk, hket⟩ := h
  refine ⟨fun x => g (k x), Coloring.map_edgePerm g hk, ?_⟩
  rw [hket, ← trace_map, List.map_map]
  rfl

/-- `c0` occurs in a permuted list exactly when it occurs in the list. -/
theorem zero_mem_map_edgePerm (g : EdgePerm) (l : List Color) :
    (0 : Color) ∈ l.map g ↔ (0 : Color) ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a, ha, hga⟩
    rwa [EdgePerm.apply_eq_zero.mp hga] at ha
  · intro h
    exact ⟨0, h, by simp⟩

/-- Completing a permuted trace permutes its completion. -/
theorem completeTrace_map (g : EdgePerm) (et : List Color) :
    completeTrace (et.map g) = (completeTrace et).map g := by
  rw [completeTrace, completeTrace, List.map_append, List.map_cons, List.map_nil, map_sum]

/-- A nonempty list summing to zero is the completion of its truncation. -/
theorem completeTrace_dropLast {l : List Color} (hne : l ≠ []) (h0 : l.sum = 0) :
    completeTrace l.dropLast = l := by
  have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
  have hsum : l.dropLast.sum + l.getLast hne = 0 := by
    have := congrArg List.sum hsplit
    rw [List.sum_append, List.sum_singleton] at this
    rw [this]; exact h0
  have hlast : l.getLast hne = l.dropLast.sum := by
    have h1 : l.dropLast.sum + (l.dropLast.sum + l.getLast hne) = l.dropLast.sum + 0 := by
      rw [hsum]
    rw [← add_assoc, Color.add_self, zero_add, add_zero] at h1
    exact h1
  rw [completeTrace, ← hlast, hsplit]

/-- The ring traces of the disk of `r`, as a predicate that does not mention the
ring proof. -/
def RTd (G : Hypermap D) (hplan : G.Planar) (r : List D) (et : List Color) : Prop :=
  ∀ h : G.Scycle G.Rlink r, (snipDisk G r hplan h).RingTrace (G.snipdRing r) et

/-- `RTd` is the ring-trace predicate of the disk. -/
theorem rTd_iff {hplan : G.Planar} {r : List D} (h : G.Scycle G.Rlink r) (et : List Color) :
    RTd G hplan r et ↔ (snipDisk G r hplan h).RingTrace (G.snipdRing r) et :=
  ⟨fun f => f h, fun x _ => x⟩

/-- `RTd` is the ring-trace predicate of the disk, as an equality of
predicates. -/
theorem rTd_eq {hplan : G.Planar} {r : List D} (h : G.Scycle G.Rlink r) :
    RTd G hplan r = (snipDisk G r hplan h).RingTrace (G.snipdRing r) :=
  funext fun et => propext (rTd_iff h et)

/-- **The geometric half of `Birkhoff_valid`**: gluing the disk of `r` to a
basis configuration produces a map smaller than `G`, hence colourable, and its
colouring supplies a ring trace of the disk that the basis tree holds. -/
theorem exists_ring_trace_of_check1 (hmin : G.MinimalCounterExample) {n m : ℕ}
    (htriv : ∀ r' : List D, G.Scycle G.Rlink r' → r'.length ≤ n → ¬ G.NontrivialRing 0 r')
    {cp : CProg} (hcp : birkhoffCheck1 n m cp = true) {r : List D}
    (hscyc : G.Scycle G.Rlink r) (hsz : r.length = n + 1) (hnt : G.NontrivialRing m r) :
    ∃ et : List Color, RTd G hmin.planar r (completeTrace et) ∧
      Ctree.mem (cpcolor cp) (evenize et) = true := by
  classical
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  have hconn := hmin.connected
  simp only [birkhoffCheck1, Bool.and_eq_true, decide_eq_true_eq] at hcp
  obtain ⟨⟨hcubQ, hcardlt⟩, hrsz⟩ := hcp
  have hcpQ : CubicProg cp := cubicProgB_iff.mp hcubQ
  -- the ring has at least two darts
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [hn0] at hsz
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsz
    exact not_scycle_singleton hbridge x (hx ▸ hscyc)
  have hrne : r ≠ [] := by intro h; rw [h] at hsz; simp at hsz
  have hbdlen : (G.snipdRing r).length = n + 1 := by rw [length_snipdRing, hsz]
  have hbdscyc := scycle_snipdRing hplan hscyc
  -- the configuration map and its reversed, rotated border
  set c := (cpmap cp).cpring with hc
  have hclen : c.length = n + 1 := by rw [hc, size_ring_cpmap, hrsz]
  set br := c.reverse.rotate (c.length - 1) with hbr
  have hbrmem : ∀ x, x ∈ br ↔ x ∈ c := by
    intro x; rw [hbr, List.mem_rotate, List.mem_reverse]
  have hbrlen : br.length = n + 1 := by rw [hbr]; simpa using hclen
  have hbrcyc : IsCyclicChain (fun u v => v = (cpmap cp).map.node u) br := by
    rw [hbr, hc]
    exact isCyclicChain_rotate.mpr isCyclicChain_reverse_cpring
  have hbrnodup : br.Nodup := by
    rw [hbr, hc]
    exact List.nodup_rotate.mpr (List.nodup_reverse.mpr nodup_cpring)
  have hlen : (G.snipdRing r).length = br.length := by rw [hbdlen, hbrlen]
  have hbdne : (G.snipdRing r) ≠ [] := by intro h; rw [h] at hbdlen; simp at hbdlen
  have hbrne : br ≠ [] := by intro h; rw [h] at hbrlen; simp at hbrlen
  obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil _ hbdne
  obtain ⟨y₀, hy₀⟩ := List.exists_mem_of_ne_nil _ hbrne
  -- the glued map
  set mt := sewMatchOf (G.snipdRing r) br x₀ y₀ hbdscyc.1 hbdscyc.nodup hbrcyc hbrnodup hlen
    with hmt
  have hP2 : Patch mt.sewMap (snipDisk G r hplan hscyc) (cpmap cp).map
      (SewMatch.sewd (br := br)) mt.sewr (G.snipdRing r) br :=
    mt.sewMap_patch hbdscyc hbrcyc hbrnodup
      (map_toDisk_sewMatchOf (G.snipdRing r) br x₀ y₀ hbdscyc.1 hbdscyc.nodup hbrcyc hbrnodup
        hlen)
  have hPd := snip_patch (G := G) (r := r) hplan hscyc
  -- the geometry of the glued map
  have hchord : (snipDisk G r hplan hscyc).Chordless (G.snipdRing r) := by
    by_contra hcon
    obtain ⟨r', hr'scyc, hr'nt, hr'len⟩ :=
      ring_disk_chord hplan hplain hbridge hconn hscyc hnt hcon
    exact htriv r' hr'scyc (by omega) hr'nt
  have hplanarG2 : mt.sewMap.Planar :=
    hP2.planar_patch.mpr ⟨planar_snipDisk hplan hscyc, cpmap_planar hcpQ⟩
  have hplainG2 : mt.sewMap.Plain :=
    hP2.plain_patch.mpr ⟨(hPd.plain_patch.mp hplain).1, cpmap_plain hcpQ⟩
  have hqcubic : (cpmap cp).map.Quasicubic br := by
    have h := cpmap_cubic hcpQ
    rw [PointedMap.Cubic, ← hc] at h
    exact ⟨fun x hx => h.1 x (fun hcm => hx ((hbrmem x).mpr hcm)),
      fun x hx => h.2 x (fun hcm => hx ((hbrmem x).mpr hcm))⟩
  have hcubicG2 : mt.sewMap.Cubic :=
    hP2.cubic_patch.mpr ⟨(hPd.cubic_patch.mp hcubic).1, hqcubic⟩
  have hbridgeG2 : mt.sewMap.Bridgeless :=
    hP2.bridgeless_patch (hPd.bridgeless hbridge).1 (cpmap_bridgeless hcpQ) hchord
  -- the glued map is smaller than `G`
  have hgeoGrr : (snipRem G r hplan hscyc).UcyclePlainQuasicubicConnected (G.sniprRing r) := by
    refine ⟨⟨⟨(hPd.plain_patch.mp hplain).2, (hPd.cubic_patch.mp hcubic).2⟩,
      isCyclicChain_sniprRing hplan hscyc, nodup_sniprRing hscyc⟩, ?_⟩
    refine hPd.connected_r hconn ⟨r.head hrne, ?_⟩
    exact fun hcon => hcon.2 (List.head_mem hrne)
  have hsrlen : (G.sniprRing r).length = n + 1 := by rw [hPd.length_br]; exact hbdlen
  have hringne : G.sniprRing r ≠ [] := by
    intro h
    have h2 := hsrlen
    rw [h] at h2
    simp at h2
  have hEuler := (quasicubic_Euler hgeoGrr hringne).mp (planar_snipRem hplan hscyc)
  have hFace := le_cycleCount_face_snipRem hplan hscyc hnt
  rw [hsrlen] at hEuler
  rw [hsz] at hFace
  have hcard2 := hP2.card_patch
  have hcardd := hPd.card_patch
  have hcardcp : Nat.card (cpmap cp).Dart = cpcard cp := card_cpmap cp
  rw [hbdlen, hcardcp] at hcard2
  rw [hbdlen] at hcardd
  have hcardlt2 : Nat.card (SewDart {x : D // G.DiskN r x} br) < Nat.card D := by omega
  -- so it is four-colourable
  have hcolG2 : mt.sewMap.FourColorable :=
    hmin.minimal mt.sewMap ⟨⟨⟨hplanarG2, hbridgeG2⟩, hplainG2⟩, hcubicG2.precubic⟩ hcardlt2
  obtain ⟨et0, hd0, hr0⟩ := hP2.colorable_patch.mp hcolG2
  obtain ⟨kd, hkd, hkdeq⟩ := hd0
  have het0len : et0.length = n + 1 := by rw [hkdeq]; simpa using hbdlen
  have het0sum : et0.sum = 0 := by rw [hkdeq]; exact sum_trace _
  have het0ne : et0 ≠ [] := by intro h; rw [h] at het0len; simp at het0len
  set et := et0.dropLast with het
  have hct : completeTrace et = et0 := completeTrace_dropLast het0ne het0sum
  have hetlen : et.length = n := by
    have h1 : et.length + 1 = et0.length := by
      rw [het, List.length_dropLast]
      omega
    omega
  refine ⟨et, ?_, ?_⟩
  · rw [hct, rTd_iff hscyc]
    exact ⟨kd, hkd, hkdeq⟩
  -- the trace lies in the basis tree
  rw [ctree_mem_cpcolor]
  refine ⟨evenTrace_evenize et, ?_⟩
  obtain ⟨kr, hkr, hkreq⟩ := hr0
  have hbrmapk : br.map kr = ((c.map kr).reverse).rotate (c.length - 1) := by
    rw [hbr, List.map_rotate, List.map_reverse]
  have hTrev : trace (br.map kr) = (trace (c.map kr)).reverse := by
    rw [hbrmapk, trace_rotate, trace_reverse, List.rotate_rotate]
    have h1 : (trace (c.map kr)).reverse.length = c.length := by simp
    rw [show 1 + (c.length - 1) = (trace (c.map kr)).reverse.length by rw [h1]; omega,
      List.rotate_length]
  rw [hTrev] at hkreq
  have hmod : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hidx : et0.length - 1 % et0.length = n := by
    rw [het0len, hmod]
    omega
  have hrotrev : et0.reverse.rotate 1 = (et0.rotate n).reverse := by
    rw [List.rotate_reverse, hidx]
  rw [hrotrev] at hkreq
  have hkey : et0.rotate n = trace (c.map kr) := List.reverse_injective hkreq
  have hrot : et0.rotate n = et.sum :: et := by
    conv_lhs => rw [← hct]
    rw [completeTrace, ← hetlen, List.rotate_append_length_eq]
    rfl
  rw [hrot] at hkey
  refine ⟨fun x => evenPerm et (kr x), Coloring.map_edgePerm (evenPerm et) hkr, ?_⟩
  have hmapc : c.map (fun x => evenPerm et (kr x)) = (c.map kr).map (evenPerm et) := by
    rw [List.map_map]; rfl
  rw [← hc, hmapc, trace_map, ← hkey]
  have hsum : (evenize et).sum = evenPerm et et.sum := by rw [evenize, map_sum]
  rw [hsum]
  rfl

/-- `RTd` is closed under colour permutations. -/
theorem RTd.map_edgePerm {hplan : G.Planar} {r : List D} (g : EdgePerm) {et : List Color}
    (h : RTd G hplan r et) : RTd G hplan r (et.map g) :=
  fun hs => RingTrace.map_edgePerm g (h hs)

/-- **The basis step**: a colouring tree passing the basis test misses a ring
trace of the disk of any `m`-nontrivial ring of the right size. -/
theorem exists_ring_trace_not_mem (hmin : G.MinimalCounterExample) {n m : ℕ}
    (htriv : ∀ r' : List D, G.Scycle G.Rlink r' → r'.length ≤ n → ¬ G.NontrivialRing 0 r')
    {cps : List CProg} (hbk1 : cps.all (birkhoffCheck1 n m) = true) {ctu : Ctree}
    (hchk : (cps.map cpcolor).any (Ctree.disjoint ctu) = true) {r : List D}
    (hscyc : G.Scycle G.Rlink r) (hsz : r.length = n + 1) (hnt : G.NontrivialRing m r) :
    ∃ et : List Color, RTd G hmin.planar r (completeTrace et) ∧
      Ctree.mem ctu (evenize et) = false := by
  obtain ⟨t, ht, hdisj⟩ := List.any_eq_true.mp hchk
  obtain ⟨cp, hcp, hteq⟩ := List.mem_map.mp ht
  subst hteq
  have hcp1 : birkhoffCheck1 n m cp = true := List.all_eq_true.mp hbk1 cp hcp
  obtain ⟨et, htr, hmem⟩ := exists_ring_trace_of_check1 hmin htriv hcp1 hscyc hsz hnt
  exact ⟨et, htr, Ctree.mem_eq_false_of_disjoint hdisj hmem⟩

/-- **One side of the elimination loop**: if the disk of `r1` has no ring trace
completing `et'`, the check for that side fails. -/
theorem doBirkhoffCheck2_side (hmin : G.MinimalCounterExample) {n' m : ℕ}
    {chkb : Ctree → Bool}
    (hchkb : ∀ ctu : Ctree, chkb ctu = true → ∀ r1 : List D, G.Scycle G.Rlink r1 →
      r1.length = n' + 2 → G.NontrivialRing m r1 →
      ∃ et : List Color, RTd G hmin.planar r1 (completeTrace et) ∧
        Ctree.mem ctu (evenize et) = false)
    {r1 : List D} (hscyc1 : G.Scycle G.Rlink r1) (hlen1 : r1.length = n' + 2)
    (hnt1 : G.NontrivialRing m r1) {ctu1 : Ctree} {gtu1 : Gtree}
    (hv1 : KempeValid n' (fun et => ¬ RTd G hmin.planar r1 et) ctu1 .empty .empty gtu1)
    {et' : List Color} (hlen' : et'.length = n' + 1)
    (hno : ¬ RTd G hmin.planar r1 (completeTrace et')) {chk : Ctree → Gtree → Bool}
    (hchk : ∀ ctu3 gtu3, KempeValid n' (fun et => ¬ RTd G hmin.planar r1 et)
      ctu3 .empty .empty gtu3 → chk ctu3 gtu3 = false)
    (hcheck : doBirkhoffCheck2 (n' + 1) chkb et' ctu1 gtu1 chk = true) : False := by
  classical
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hconn := hmin.connected
  have hcubic := hmin.cubic
  have hproper1 := nontrivialRing_properRing hplan hplain hbridge hconn hscyc1 hnt1
  have hclosed : KempeClosed (RTd G hmin.planar r1) := by
    rw [rTd_eq hscyc1]
    exact ring_disk_closed hplan hplain hconn hscyc1 hproper1 hcubic
  rw [doBirkhoffCheck2] at hcheck
  split_ifs at hcheck with h0
  simp only [Nat.add_sub_cancel, Bool.and_eq_true, Bool.or_eq_true] at hcheck
  obtain ⟨hgtr, hor⟩ := hcheck
  -- the restricted state is valid
  have h0' : (0 : Color) ∉ evenize et' := by
    rw [evenize, zero_mem_map_edgePerm]
    exact h0
  have hrestr : ∀ et1, Ctree.mem (Ctree.ofTrace (evenize et')) et1 = true →
      (¬ RTd G hmin.planar r1 (completeTrace et1)) ∧ et1.length = n' + 1 := by
    intro et1 hm
    have heq : et1 = evenize et' := (Ctree.mem_ofTrace _ h0' et1).mp hm
    subst heq
    refine ⟨?_, by rw [evenize, List.length_map]; exact hlen'⟩
    rw [evenize, completeTrace_map]
    intro hcc
    refine hno ?_
    have h2 := RTd.map_edgePerm ((evenPerm et')⁻¹) hcc
    rwa [map_map_edgePerm, inv_mul_cancel, map_one_edgePerm] at h2
  have hvr := kempeValid_restrict hrestr hv1
  obtain ⟨hvalid3, -⟩ :=
    kempeTreeClosure_correct n' (fun et => ¬ RTd G hmin.planar r1 et) (n' + 1) ctu1
      (Ctree.ofTrace (evenize et')) gtu1 hvr
  rw [Gtree.isEmpty_eq_true] at hgtr
  rcases hor with hb | hc
  · obtain ⟨et1, htr1, hnm1⟩ :=
      hchkb _ hb r1 hscyc1 hlen1 hnt1
    have hlen1' : et1.length = n' + 1 := by
      obtain ⟨k, -, hk⟩ := htr1 hscyc1
      have h3 := congrArg List.length hk
      rw [completeTrace, List.length_append, length_trace, List.length_map,
        length_snipdRing, hlen1] at h3
      simp at h3
      omega
    obtain ⟨et2, hnot, hyes⟩ :=
      kempeCoclosure_of_not_mem hvalid3 hlen1' hnm1 (RTd G hmin.planar r1) hclosed htr1
    exact hnot hyes
  · rw [hchk _ _ (by rw [← hgtr]; exact hvalid3)] at hc
    simp at hc

/-- **The elimination loop fails**: in a minimal counter-example with an
`m`-nontrivial ring of `n' + 2` darts, no number of rounds makes the check
succeed. -/
theorem birkhoffCheck2_eq_false (hmin : G.MinimalCounterExample) {n' m : ℕ}
    {chkb : Ctree → Bool}
    (hchkb : ∀ ctu : Ctree, chkb ctu = true → ∀ r1 : List D, G.Scycle G.Rlink r1 →
      r1.length = n' + 2 → G.NontrivialRing m r1 →
      ∃ et : List Color, RTd G hmin.planar r1 (completeTrace et) ∧
        Ctree.mem ctu (evenize et) = false) :
    ∀ (niter : ℕ) (r1 : List D) (ctu1 : Ctree) (gtu1 : Gtree) (ctu2 : Ctree) (gtu2 : Gtree),
      G.Scycle G.Rlink r1 → r1.length = n' + 2 → G.NontrivialRing m r1 →
      KempeValid n' (fun et => ¬ RTd G hmin.planar r1 et) ctu1 .empty .empty gtu1 →
      KempeValid n' (fun et => ¬ RTd G hmin.planar (G.revRing r1) et) ctu2 .empty .empty gtu2 →
      birkhoffCheck2 (n' + 1) chkb niter ctu1 gtu1 ctu2 gtu2 = false := by
  classical
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hconn := hmin.connected
  intro niter
  induction niter with
  | zero => intro r1 ctu1 gtu1 ctu2 gtu2 _ _ _ _ _; rfl
  | succ k ih =>
    intro r1 ctu1 gtu1 ctu2 gtu2 hscyc1 hlen1 hnt1 hv1 hv2
    have hproper1 := nontrivialRing_properRing hplan hplain hbridge hconn hscyc1 hnt1
    have hscyc2 : G.Scycle G.Rlink (G.revRing r1) := scycle_revRing hplain hscyc1
    have hnt2 : G.NontrivialRing m (G.revRing r1) :=
      nontrivial_revRing hplan hplain hbridge hconn hscyc1 hnt1
    have hlen2 : (G.revRing r1).length = n' + 2 := by
      rw [Hypermap.revRing, List.length_reverse, List.length_map]; exact hlen1
    have hrr : G.revRing (G.revRing r1) = r1 := revRing_revRing hplain r1
    simp only [birkhoffCheck2]
    cases hpick : ctreePickRev ctu1 ctu2 with
    | nil => rfl
    | cons e et =>
      have hsumEt : (e :: et).sum = 0 := by
        rw [← hpick]; exact sum_ctreePickRev ctu1 ctu2
      have hlenEt : et.length = n' + 1 := by
        rcases length_ctreePickRev hv2.proper ctu1 with h | h
        · rw [hpick] at h; simp at h
        · rw [hpick] at h; simp only [List.length_cons] at h; omega
      have hct1 : completeTrace ((e :: et).dropLast) = e :: et :=
        completeTrace_dropLast (by simp) hsumEt
      have hetsum : et.sum = e := by
        have h1 : e + et.sum = 0 := by rw [← List.sum_cons]; exact hsumEt
        have h2 : e + (e + et.sum) = e + 0 := by rw [h1]
        rw [← add_assoc, Color.add_self, zero_add, add_zero] at h2
        exact h2
      have hct2 : completeTrace et.reverse = (e :: et).reverse := by
        rw [completeTrace, List.sum_reverse, hetsum]
        simp
      refine Bool.eq_false_iff.mpr fun hcon => ?_
      rw [Bool.and_eq_true] at hcon
      obtain ⟨hA, hB⟩ := hcon
      refine hmin.noncolorable ?_
      refine colorable_from_ring hplan hplain hconn hscyc1 hproper1 (et := e :: et) ?_ ?_
      · by_contra hno
        rw [← rTd_iff hscyc1, ← hct1] at hno
        refine doBirkhoffCheck2_side hmin hchkb hscyc1 hlen1 hnt1 hv1 ?_ hno ?_ hA
        · simp only [List.length_dropLast, List.length_cons]
          omega
        · intro ctu3 gtu3 hv3
          refine ih (G.revRing r1) ctu2 gtu2 ctu3 gtu3 hscyc2 hlen2 hnt2 hv2 ?_
          rw [hrr]
          exact hv3
      · by_contra hno
        rw [show (G.revSnipDisk r1 hplan hplain hscyc1) =
            snipDisk G (G.revRing r1) hplan hscyc2 from rfl,
          show (G.revSnipdRing r1) = G.snipdRing (G.revRing r1) from rfl,
          ← rTd_iff hscyc2, ← hct2] at hno
        refine doBirkhoffCheck2_side hmin hchkb hscyc2 hlen2 hnt2 hv2 ?_ hno ?_ hB
        · simp only [List.length_reverse]
          exact hlenEt
        · intro ctu3 gtu3 hv3
          exact ih r1 ctu1 gtu1 ctu3 gtu3 hscyc1 hlen1 hnt1 hv1 hv3

omit [DecidableEq D] in
/-- **Birkhoff's lemma from a check**: a reducibility check for ring size
`n + 1` rules out `m`-nontrivial rings of that size, given that shorter rings
are already known to be trivial. -/
theorem birkhoff_valid (hmin : G.MinimalCounterExample) {n m : ℕ}
    (htriv : ∀ r' : List D, G.Scycle G.Rlink r' → r'.length ≤ n → ¬ G.NontrivialRing 0 r')
    (hchk : BirkhoffCheck n m) {r : List D} (hscyc : G.Scycle G.Rlink r)
    (hsz : r.length = n + 1) : ¬ G.NontrivialRing m r := by
  classical
  intro hnt
  obtain ⟨niter, cps, hbk1, hbk2⟩ := hchk
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    rw [hn0] at hsz
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsz
    exact not_scycle_singleton hmin.bridgeless x (hx ▸ hscyc)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hloop := birkhoffCheck2_eq_false hmin
    (chkb := fun t => (cps.map cpcolor).any (Ctree.disjoint t))
    (fun ctu hc r1 h1 hl1 hnt1 =>
      exists_ring_trace_not_mem hmin htriv hbk1 hc h1 (by omega) hnt1)
    niter r (initTree (n' + 1)) (gtreeInitTree (n' + 1)) (initTree (n' + 1))
    (gtreeInitTree (n' + 1)) hscyc (by omega) hnt (kempeValid_init n' _) (kempeValid_init n' _)
  rw [hloop] at hbk2
  simp at hbk2

/-! ### Birkhoff's lemma

The four checks, fed to `birkhoff_valid` one ring size at a time, rule out every
nontrivial ring of at most five darts. -/

omit [DecidableEq D] in
/-- The induction over ring sizes: rings of at most `n ≤ 5` darts are never
nontrivial. -/
private theorem birkhoff_aux (hmin : G.MinimalCounterExample) :
    ∀ n, n ≤ 5 → ∀ r : List D, r.length ≤ n → G.Scycle G.Rlink r →
      ¬ G.NontrivialRing (if r.length = 5 then 1 else 0) r := by
  classical
  intro n
  induction n with
  | zero =>
    intro _ r hlen _
    have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    exact not_nontrivialRing_nil _
  | succ n ih =>
    intro hn5 r hlen hscyc
    rcases Nat.lt_or_ge r.length (n + 1) with hlt | hge
    · exact ih (by omega) r (by omega) hscyc
    have hsz : r.length = n + 1 := by omega
    have htriv : ∀ r' : List D, G.Scycle G.Rlink r' → r'.length ≤ n →
        ¬ G.NontrivialRing 0 r' := by
      intro r' hs' hl'
      have h := ih (by omega) r' hl' hs'
      have hne : ¬ (r'.length = 5) := by omega
      simpa [hne] using h
    have hn4 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rw [hsz]
    rcases hn4 with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsz
      exact absurd (hx ▸ hscyc) (not_scycle_singleton hmin.bridgeless x)
    · simpa using birkhoff_valid hmin htriv birkhoffCheck_one_zero hscyc hsz
    · simpa using birkhoff_valid hmin htriv birkhoffCheck_two_zero hscyc hsz
    · simpa using birkhoff_valid hmin htriv birkhoffCheck_three_zero hscyc hsz
    · simpa using birkhoff_valid hmin htriv birkhoffCheck_four_one hscyc hsz

omit [DecidableEq D] in
/-- **Birkhoff's lemma**: a minimal counter-example to the Four Colour Theorem
is internally five-connected — no ring of at most five darts separates two
nontrivial parts of the map. -/
theorem MinimalCounterExample.birkhoffRings (hmin : G.MinimalCounterExample) :
    G.BirkhoffRings :=
  fun r hlen hscyc => birkhoff_aux hmin 5 le_rfl r hlen hscyc

omit [DecidableEq D] in
/-- **A minimal counter-example is pentagonal.** -/
theorem MinimalCounterExample.pentagonal (hmin : G.MinimalCounterExample) : G.Pentagonal :=
  hmin.pentagonal_of_birkhoff hmin.birkhoffRings

omit [DecidableEq D] in
/-- **A minimal counter-example is plain, cubic and pentagonal**, which is what
the reducibility arguments consume. -/
theorem MinimalCounterExample.plainCubicPentagonal (hmin : G.MinimalCounterExample) :
    G.PlainCubicPentagonal :=
  hmin.plainCubicPentagonal_of_birkhoff hmin.birkhoffRings

end BirkhoffValid

end Hypermap

end FourColor

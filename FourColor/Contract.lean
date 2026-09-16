import FourColor.Birkhoff

/-!
# Contracts in a minimal counter-example

A *contract* for a configuration is a short list `cc` of darts whose E-links are
to be collapsed.  This file develops the theory of contracts in a minimal
counter-example: it introduces `Hypermap.ContractRing`, the rings that a
contract would collapse to a single dart, shows that a valid contract admits no
such ring, and deduces that every valid contract has a contract colouring.

The last statement, `Hypermap.contract_coloring`, is what the embedding
development consumes: contract validity is preserved by an embedding except for
the ring condition, which becomes moot.

## Status

Pentagonality of a minimal counter-example is not yet unconditional in this
port: it is derived in `FourColor/Birkhoff.lean` from the hypothesis
`Hypermap.BirkhoffRings`, which still waits on one lemma of the Birkhoff
development.  Every statement below that needs it therefore carries
`hB : G.BirkhoffRings` as an extra hypothesis; once `BirkhoffRings` becomes a
theorem all of them are discharged by a single substitution.

The reference's `contract_coloring` appears here as
`Hypermap.MinimalCounterExample.contract_coloring`; the bare name
`Hypermap.contract_coloring` is already taken by an unrelated result of
`FourColor/Kempe.lean`.

## Main definitions

* `Hypermap.ContractRing` — `r` is a proper ring that the contract `cc`
  collapses to its head, i.e. the rest of `r` lies in the edge closure of `cc`.

## Main results

* `Hypermap.sparse_contract_ring` — a contract ring of a node-simple contract
  is a nontrivial ring.
* `Hypermap.contract_ring_max` — a contract ring has at most one dart more than
  its contract.
* `Hypermap.contract3_valid`, `Hypermap.triad_valid` — a node-simple contract of
  at most three darts, and one of four darts with a triad, admit no contract
  ring.
* `Hypermap.MinimalCounterExample.contract_coloring` — the reference's
  `contract_coloring`: every valid contract has a contract colouring.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file corresponds
to `theories/proof/contract.v` of the Coq development.
-/


namespace FourColor

namespace Hypermap

open Equiv Equiv.Perm

variable {D : Type*} {G : Hypermap D}

section Finite

variable [Finite D]

/-! ### Counting the faces met by a list -/

open scoped Classical in
/-- Adding a face to a set of darts adds one to its face count. -/
private theorem faceCard_cons {a : D} {B : D → Prop} (h : ∀ z, B z → ¬ G.CFace z a) :
    G.faceCard (fun z => G.CFace z a ∨ B z) = G.faceCard B + 1 := by
  classical
  have himg : (Quotient.mk (SameCycle.setoid G.face) '' {z | G.CFace z a ∨ B z})
      = insert (Quotient.mk (SameCycle.setoid G.face) a)
        (Quotient.mk (SameCycle.setoid G.face) '' {z | B z}) := by
    ext c
    constructor
    · rintro ⟨z, hz | hz, rfl⟩
      · exact Set.mem_insert_iff.mpr (Or.inl (Quotient.sound hz))
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨z, hz, rfl⟩)
    · intro hc
      rcases Set.mem_insert_iff.mp hc with rfl | ⟨z, hz, rfl⟩
      · exact ⟨a, Or.inl (SameCycle.refl _ _), rfl⟩
      · exact ⟨z, Or.inr hz, rfl⟩
  have hnot : Quotient.mk (SameCycle.setoid G.face) a
      ∉ Quotient.mk (SameCycle.setoid G.face) '' {z | B z} := by
    rintro ⟨z, hz, hzq⟩
    exact h z hz (Quotient.exact hzq)
  rw [faceCard, faceCard, himg, Set.ncard_insert_of_notMem hnot (Set.toFinite _)]

/-- The band of a face-simple list meets exactly as many faces as the list has
darts.  This is the reference's `scycle_fcard_fband`. -/
theorem faceCard_fband_of_simple {p : List D} (hs : G.Simple p) :
    G.faceCard (G.Fband p) = p.length := by
  induction p with
  | nil =>
    rw [faceCard_eq_zero (fun z => fband_nil z)]
    rfl
  | cons a l ih =>
    obtain ⟨hna, hsl⟩ := simple_cons.mp hs
    have heq : ∀ z, G.Fband (a :: l) z ↔ (G.CFace z a ∨ G.Fband l z) := fun _ => fband_cons
    rw [faceCard_congr heq,
      faceCard_cons (fun z hz hc => hna ((Fband.congr hc).mp hz)), ih hsl]
    simp

open scoped Classical in
/-- A set of darts meeting strictly fewer faces than another: every face it
meets is met by the larger set, which moreover meets a face it misses. -/
theorem faceCard_lt_faceCard {A B : D → Prop} (hsub : ∀ z, A z → B z) {w : D}
    (hw : B w) (hnew : ∀ z, A z → ¬ G.CFace z w) : G.faceCard A < G.faceCard B := by
  classical
  refine Set.ncard_lt_ncard ⟨fun c hc => ?_, fun hc => ?_⟩ (Set.toFinite _)
  · obtain ⟨z, hz, rfl⟩ := hc
    exact ⟨z, hsub z hz, rfl⟩
  · obtain ⟨z, hz, hzw⟩ := hc ⟨w, hw, rfl⟩
    exact hnew z hz (Quotient.exact hzw)

/-! ### Contract rings -/

omit [Finite D] in
/-- Two distinct darts of a node-simple list share no node. -/
theorem sparse_not_cnode {p : List D} (h : G.Sparse p) {a b : D}
    (ha : a ∈ p) (hb : b ∈ p) (hab : a ≠ b) : ¬ G.CNode a b := by
  induction p with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons c l ih =>
    obtain ⟨hc, hl⟩ := sparse_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact hc b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact fun hcn => hc a ha' hcn.symm
      · exact ih hl ha' hb'

variable (G) in
/-- `r` is a *contract ring* for `cc`: a proper ring that the contract `cc`
collapses to its first dart, in the sense that all its other darts lie in the
edge closure of `cc`. -/
structure ContractRing (cc r : List D) : Prop where
  /-- `r` is a face-simple `Rlink` cycle. -/
  scycle : G.Scycle G.Rlink r
  /-- `r` is not empty and not an edge orbit. -/
  proper : G.ProperRing r
  /-- All darts of `r` but the first are contracted. -/
  tail_mem : ∀ z ∈ r.tail, z ∈ G.insertE cc

open scoped Classical in
omit [Finite D] in
/-- The tail of a chord ring is the arc it closes. -/
private theorem tail_chordRing (G : Hypermap D) (r : List D) (x : D) :
    (G.chordRing r x).tail = arc r (G.fproj r (G.edge x)) (G.fproj r x) := rfl

open scoped Classical in
/-- A chord of a contract ring whose arc misses the head of the ring cuts out a
shorter contract ring. -/
private theorem contractRing_chordRing (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) {cc : List D} {x : D} {t : List D}
    (hcr : G.ContractRing cc (x :: t)) {c : D} (hdEc : G.DiskE (x :: t) c)
    (hcb : G.Fband (x :: t) c) (hceb : G.Fband (x :: t) (G.edge c))
    (hnx : x ∉ (G.chordRing (x :: t) c).tail) :
    G.ContractRing cc (G.chordRing (x :: t) c) := by
  classical
  refine ⟨scycle_chordRing hplain hbridge hcr.scycle hcb hceb,
    properRing_chordRing hplan hplain hbridge hcr.scycle hdEc hcb hceb, fun z hz => ?_⟩
  have hzp : z ∈ x :: t := mem_of_mem_arc (l := x :: t) hz
  have hzx : z ≠ x := fun h => hnx (h ▸ hz)
  exact hcr.tail_mem z ((List.mem_cons.mp hzp).resolve_left hzx)

open scoped Classical in
omit [Finite D] in
/-- A chord whose two ends are not cyclically consecutive on the ring cuts out a
strictly shorter ring. -/
private theorem length_chordRing_lt (hplain : G.Plain) (hbridge : G.Bridgeless)
    {r : List D} (hscyc : G.Scycle G.Rlink r) {x : D} (hxb : G.Fband r x)
    (hexb : G.Fband r (G.edge x))
    (hnc : ¬ CyclicNext r (G.fproj r x) (G.fproj r (G.edge x))) :
    (G.chordRing r x).length < r.length := by
  classical
  obtain ⟨p, q, hcr1, -, n, hn⟩ := exists_chordRing_split hplain hbridge hscyc hxb hexb
  have hlenr : r.length = (p.length + 1) + (q.length + 1) := by
    have h := congrArg List.length hn
    rw [List.length_rotate] at h
    simp only [List.length_append, List.length_cons] at h
    omega
  have hq : q ≠ [] := by
    rintro rfl
    refine hnc ⟨n + (G.fproj r (G.edge x) :: p).length, G.fproj r (G.edge x) :: p, ?_, rfl⟩
    rw [← List.rotate_rotate, hn, List.rotate_append_length_eq]
    rfl
  have hqpos : 0 < q.length := List.length_pos_iff.mpr hq
  have hlen1 : (G.chordRing r x).length = p.length + 1 + 1 := by rw [hcr1]; simp
  omega


/-! ### A contract ring of a node-simple contract is nontrivial -/

open scoped Classical in
/-- The inductive step of `Hypermap.sparse_contract_ring`: assuming the result
for shorter rings, a contract ring has a face strictly inside it.  If it did
not, the two node-successors of its head would both lie on the ring or cut it
with a chord; the chord case is handled by induction, and in the remaining case
the two successors are both contracted, contradicting node-simplicity. -/
private theorem exists_diskF_step (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hconn : G.Connected)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) {p : List D}
    (ih : ∀ q : List D, q.length < p.length → G.ContractRing cc q → ∃ y, G.DiskF q y)
    (hcr : G.ContractRing cc p) : ∃ y, G.DiskF p y := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  have hscyc := hcr.scycle
  have hproper := hcr.proper
  have hnodup : p.Nodup := hscyc.nodup
  obtain ⟨x, t, rfl⟩ : ∃ x t, p = x :: t := by
    rcases p with _ | ⟨x, t⟩
    · exact hproper.elim
    · exact ⟨x, t, rfl⟩
  have hxmem : x ∈ x :: t := List.mem_cons_self ..
  have hdNx : G.DiskN (x :: t) x := diskN_of_mem hxmem
  -- the two node-successors of the head lie in the band of the ring
  have hFnx : G.Fband (x :: t) (G.node x) := by
    by_contra hb
    exact hcon (G.node x) ⟨diskN_node_iff.mpr hdNx, hb⟩
  have hFnnx : G.Fband (x :: t) (G.node (G.node x)) := by
    by_contra hb
    exact hcon (G.node (G.node x)) ⟨diskN_node_iff.mpr (diskN_node_iff.mpr hdNx), hb⟩
  have hjmem : G.fproj (x :: t) (G.node x) ∈ x :: t := G.fproj_mem hFnx
  have hjF : G.CFace (G.node x) (G.fproj (x :: t) (G.node x)) := G.cface_fproj _
  have hne_jx : G.fproj (x :: t) (G.node x) ≠ x := by
    intro h
    rw [h] at hjF
    exact hbridge.not_cface_node x hjF
  -- the dart following the head on the ring
  have hRx1 : G.Rlink x ((x :: t).next x hxmem) :=
    rel_next hscyc.isCyclicChain hnodup hxmem
  have hcn : CyclicNext (x :: t) x ((x :: t).next x hxmem) :=
    (cyclicNext_iff_next hnodup hxmem).mpr rfl
  have hne_jx1 : G.fproj (x :: t) (G.node x) ≠ (x :: t).next x hxmem := by
    intro h
    rw [h] at hjF
    have h2 : G.CFace (G.node x) (G.edge x) := hjF.trans hRx1.symm
    have h3 : G.CFace (G.edge x) (G.node (G.node x)) := by
      rw [hcubic.node_node x]; exact G.cface_face (G.edge x)
    exact hbridge.not_cface_node (G.node x) (h2.trans h3).symm
  -- the first node-successor lies on the ring
  have hnxmem : G.node x ∈ x :: t := by
    by_contra hnm
    have hdEnx : G.DiskE (x :: t) (G.node x) := ⟨diskN_node_iff.mpr hdNx, hnm⟩
    have hcF : G.CFace (G.edge (G.node x)) x := G.cface_edge_node x
    have hcb : G.Fband (x :: t) (G.edge (G.node x)) := ⟨x, hxmem, hcF⟩
    have hceb : G.Fband (x :: t) (G.edge (G.edge (G.node x))) := by
      rw [hplain.edge_edge]; exact hFnx
    have hdEc : G.DiskE (x :: t) (G.edge (G.node x)) := diskE_edge hplan hscyc hdEnx
    have hfc : G.fproj (x :: t) (G.edge (G.node x)) = x := hscyc.simple.fproj_eq hxmem hcF
    have hfec : G.fproj (x :: t) (G.edge (G.edge (G.node x)))
        = G.fproj (x :: t) (G.node x) := by rw [hplain.edge_edge]
    obtain ⟨P, Q, hA, -, n, hn⟩ := exists_arc_split hnodup hjmem hxmem hne_jx
    have hnd : ((G.fproj (x :: t) (G.node x) :: P) ++ (x :: Q)).Nodup := by
      rw [← hn]; exact List.nodup_rotate.mpr hnodup
    have htail : x ∉ (G.chordRing (x :: t) (G.edge (G.node x))).tail := by
      rw [tail_chordRing, hfc, hfec, hA]
      obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
      exact fun hc => hdisj x hc x List.mem_cons_self rfl
    have hcr2 := contractRing_chordRing hplan hplain hbridge hcr hdEc hcb hceb htail
    have hlt : (G.chordRing (x :: t) (G.edge (G.node x))).length < (x :: t).length := by
      refine length_chordRing_lt hplain hbridge hscyc hcb hceb ?_
      rw [hfc, hfec]
      intro hcyc
      exact hne_jx1 (cyclicNext_functional hnodup hcyc hcn)
    obtain ⟨y, hy⟩ := ih _ hlt hcr2
    exact hcon y
      ((diskF_chordRing hplan hplain hbridge hconn hscyc hproper hdEc hcb hceb).mp hy).1
  -- the head follows the first node-successor on the ring
  have hnextnx : (x :: t).next (G.node x) hnxmem = x :=
    hscyc.simple.eq_of_cface (List.next_mem _ _ _) hxmem
      ((rel_next hscyc.isCyclicChain hnodup hnxmem).symm.trans (G.cface_edge_node x))
  have hcnnx : CyclicNext (x :: t) (G.node x) x :=
    (cyclicNext_iff_next hnodup hnxmem).mpr hnextnx.symm
  have hne_j'x : G.fproj (x :: t) (G.node (G.node x)) ≠ x := by
    intro h
    have h1 : G.CFace (G.node (G.node x)) x := by
      have hf := G.cface_fproj (p := x :: t) (G.node (G.node x))
      rwa [h] at hf
    rw [hcubic.node_node x] at h1
    exact hbridge x ((G.cface_face (G.edge x)).trans h1).symm
  have hne_j'nx : G.fproj (x :: t) (G.node (G.node x)) ≠ G.node x := by
    intro h
    have h1 : G.CFace (G.node (G.node x)) (G.node x) := by
      have hf := G.cface_fproj (p := x :: t) (G.node (G.node x))
      rwa [h] at hf
    exact hbridge.not_cface_node (G.node x) h1
  -- the second node-successor lies on the ring
  have hnnxmem : G.node (G.node x) ∈ x :: t := by
    by_contra hnm
    have hdEnnx : G.DiskE (x :: t) (G.node (G.node x)) :=
      ⟨diskN_node_iff.mpr (diskN_node_iff.mpr hdNx), hnm⟩
    have hcF : G.CFace (G.edge (G.node (G.node x))) (G.node x) := G.cface_edge_node (G.node x)
    have hcb : G.Fband (x :: t) (G.edge (G.node (G.node x))) := ⟨G.node x, hnxmem, hcF⟩
    have hceb : G.Fband (x :: t) (G.edge (G.edge (G.node (G.node x)))) := by
      rw [hplain.edge_edge]; exact hFnnx
    have hdEc : G.DiskE (x :: t) (G.edge (G.node (G.node x))) :=
      diskE_edge hplan hscyc hdEnnx
    have hfc : G.fproj (x :: t) (G.edge (G.node (G.node x))) = G.node x :=
      hscyc.simple.fproj_eq hnxmem hcF
    have hfec : G.fproj (x :: t) (G.edge (G.edge (G.node (G.node x))))
        = G.fproj (x :: t) (G.node (G.node x)) := by rw [hplain.edge_edge]
    obtain ⟨P, Q, hA, -, n, hn⟩ :=
      exists_arc_split hnodup (G.fproj_mem hFnnx) hnxmem hne_j'nx
    have hrot2 : (x :: t).rotate (n + (G.fproj (x :: t) (G.node (G.node x)) :: P).length)
        = (G.node x :: Q) ++ (G.fproj (x :: t) (G.node (G.node x)) :: P) := by
      rw [← List.rotate_rotate, hn, List.rotate_append_length_eq]
    have hnd : ((G.fproj (x :: t) (G.node (G.node x)) :: P) ++ (G.node x :: Q)).Nodup := by
      rw [← hn]; exact List.nodup_rotate.mpr hnodup
    have hxQ : x ∈ G.node x :: Q := by
      rcases Q with _ | ⟨z, Q'⟩
      · exact absurd (cyclicNext_functional hnodup
          (⟨_, _, hrot2, rfl⟩ : CyclicNext (x :: t) (G.node x)
            (G.fproj (x :: t) (G.node (G.node x)))) hcnnx) hne_j'x
      · have hxz : x = z :=
          cyclicNext_functional hnodup hcnnx (⟨_, _, hrot2, rfl⟩ : CyclicNext _ _ z)
        rw [hxz]
        exact List.mem_cons_of_mem _ List.mem_cons_self
    have htail : x ∉ (G.chordRing (x :: t) (G.edge (G.node (G.node x)))).tail := by
      rw [tail_chordRing, hfc, hfec, hA]
      obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
      exact fun hc => hdisj x hc x hxQ rfl
    have hcr2 := contractRing_chordRing hplan hplain hbridge hcr hdEc hcb hceb htail
    have hlt :
        (G.chordRing (x :: t) (G.edge (G.node (G.node x)))).length < (x :: t).length := by
      refine length_chordRing_lt hplain hbridge hscyc hcb hceb ?_
      rw [hfc, hfec]
      intro hcyc
      exact hne_j'x (cyclicNext_functional hnodup hcyc hcnnx)
    obtain ⟨y, hy⟩ := ih _ hlt hcr2
    exact hcon y
      ((diskF_chordRing hplan hplain hbridge hconn hscyc hproper hdEc hcb hceb).mp hy).1
  -- both node-successors of the head are contracted, contradicting sparsity
  have hccnx : G.node x ∈ G.insertE cc :=
    hcr.tail_mem _ ((List.mem_cons.mp hnxmem).resolve_left (hcubic.node_ne x))
  have hnnne : G.node (G.node x) ≠ x := by
    intro h
    have h3 := hcubic.node_node_node x
    rw [h] at h3
    exact hcubic.node_ne x h3
  have hccnnx : G.node (G.node x) ∈ G.insertE cc :=
    hcr.tail_mem _ ((List.mem_cons.mp hnnxmem).resolve_left hnnne)
  have hnenn : G.node x ≠ G.node (G.node x) := fun h =>
    hcubic.node_ne x (G.node.injective h).symm
  exact sparse_not_cnode hsp hccnx hccnnx hnenn
    (sameCycle_apply_right.mpr (SameCycle.refl _ _))

/-- Every contract ring of a node-simple contract has a face strictly inside
it, by induction on its length. -/
private theorem exists_diskF_aux (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hconn : G.Connected)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) :
    ∀ (n : ℕ) (p : List D), p.length ≤ n → G.ContractRing cc p → ∃ y, G.DiskF p y := by
  intro n
  induction n with
  | zero =>
    intro p hlen hcr
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hp
    exact hcr.proper.elim
  | succ n ih =>
    intro p hlen hcr
    exact exists_diskF_step hplan hplain hbridge hcubic hconn hsp
      (fun q hq hcrq => ih q (by omega) hcrq) hcr

/-- Every contract ring of a node-simple contract has a face strictly inside
it. -/
private theorem exists_diskF_of_contractRing (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hconn : G.Connected)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) (p : List D)
    (hcr : G.ContractRing cc p) : ∃ y, G.DiskF p y :=
  exists_diskF_aux hplan hplain hbridge hcubic hconn hsp p.length p le_rfl hcr

/-- **A contract ring of a node-simple contract is a nontrivial ring.**  This is
the reference's `sparse_contract_ring`. -/
theorem sparse_contract_ring (hplan : G.Planar) (hplain : G.Plain)
    (hbridge : G.Bridgeless) (hcubic : G.Cubic) (hconn : G.Connected)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) {p : List D}
    (hcr : G.ContractRing cc p) : G.NontrivialRing 0 p := by
  classical
  have hmain := exists_diskF_of_contractRing hplan hplain hbridge hcubic hconn hsp
  refine nontrivialRing_zero_iff.mpr ⟨hmain p hcr, ?_⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, p = x :: t := by
    rcases p with _ | ⟨x, t⟩
    · exact hcr.proper.elim
    · exact ⟨x, t, rfl⟩
  have hrot : (x :: t).rotate 1 = t ++ [x] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  have hscycrot : G.Scycle G.Rlink ((x :: t).rotate 1) := scycle_rotate.mpr hcr.scycle
  have hproprot : G.ProperRing ((x :: t).rotate 1) := (properRing_rotate hplain).mpr hcr.proper
  have hqeq : G.revRing ((x :: t).rotate 1) = G.edge x :: (t.map G.edge).reverse := by
    rw [hrot, revRing]
    simp
  have hcrq : G.ContractRing cc (G.revRing ((x :: t).rotate 1)) := by
    refine ⟨scycle_revRing hplain hscycrot, (properRing_revRing hplain).mpr hproprot, ?_⟩
    intro z hz
    rw [hqeq] at hz
    simp only [List.tail_cons, List.mem_reverse, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨u, hu, hwu⟩ := (mem_insertE hplain).mp (hcr.tail_mem w hw)
    exact (mem_insertE hplain).mpr
      ⟨u, hu, (sameCycle_apply_left.mpr (SameCycle.refl _ _)).trans hwu⟩
  obtain ⟨y, hy⟩ := hmain _ hcrq
  refine ⟨y, ?_⟩
  have h1 := (diskF_revRing hplan hplain hconn hscycrot hproprot (x := y)).mp hy
  rwa [diskFC_rotate] at h1

/-! ### The size of a contract ring -/

/-- **A contract ring has at most one dart more than its contract.**  This is
the reference's `contract_ring_max`. -/
theorem contract_ring_max (hplan : G.Planar) (hplain : G.Plain) {cc p : List D}
    (hcr : G.ContractRing cc p) : p.length ≤ cc.length + 1 := by
  classical
  obtain ⟨x, t, rfl⟩ : ∃ x t, p = x :: t := by
    rcases p with _ | ⟨x, t⟩
    · exact hcr.proper.elim
    · exact ⟨x, t, rfl⟩
  have hnodup : (x :: t).Nodup := hcr.scycle.nodup
  have htnd : t.Nodup := hnodup.of_cons
  have hchoice : ∀ z ∈ t, ∃ y, y ∈ cc ∧ G.CEdge z y := fun z hz =>
    (mem_insertE hplain).mp (hcr.tail_mem z hz)
  choose! f hf hfE using hchoice
  have hinj : ∀ a ∈ t, ∀ b ∈ t, f a = f b → a = b := by
    intro a ha b hb hab
    have h1 : G.CEdge a (f a) := hfE a ha
    have h2 : G.CEdge b (f a) := by rw [hab]; exact hfE b hb
    rcases hplain.cedge_iff.mp (h1.trans h2.symm) with h | h
    · exact h.symm
    · exact absurd (by rw [← h]; exact diskN_of_mem (List.mem_cons_of_mem x hb))
        (diskN_edge_ring hplan hplain hcr.scycle hcr.proper (List.mem_cons_of_mem x ha))
  have hsub : t.map f ⊆ cc := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hf z hz
  have hlen : (t.map f).length ≤ cc.length :=
    (List.subperm_of_subset (List.Nodup.map_on hinj htnd) hsub).length_le
  simp only [List.length_map] at hlen
  simp only [List.length_cons]
  omega

/-! ### Small contracts admit no contract ring -/

/-- **A node-simple contract of at most three darts admits no contract ring.**
This is the reference's `contract3_valid`. -/
theorem contract3_valid (hmin : G.MinimalCounterExample) (hB : G.BirkhoffRings)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) (hle : cc.length ≤ 3) (p : List D) :
    ¬ G.ContractRing cc p := by
  intro hcr
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  have hconn := hmin.connected
  have hlen : p.length ≤ cc.length + 1 := contract_ring_max hplan hplain hcr
  have h5 : ¬ (p.length = 5) := by omega
  have hif : (if p.length = 5 then (1 : ℕ) else 0) = 0 := by simp [h5]
  refine hB p (by omega) hcr.scycle ?_
  rw [hif]
  exact sparse_contract_ring hplan hplain hbridge hcubic hconn hsp hcr


/-! ### Contracts of four darts with a triad -/

omit [Finite D] in
/-- The outside of a disk, in terms of the face-closed disk. -/
private theorem diskFC_iff {r : List D} {u : D} :
    G.DiskFC r u ↔ ¬ G.Fband r u ∧ ¬ G.DiskF r u := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun hc => h1 hc.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h2 ⟨hc, h1⟩, h1⟩

/-- The outside of a disk only depends on the face of a dart. -/
private theorem diskFC_congr {r : List D} {u v : D} (h : G.CFace u v) :
    G.DiskFC r u ↔ G.DiskFC r v := by
  rw [diskFC_iff, diskFC_iff, Fband.congr (p := r) h, diskF_congr (s := r) h]

/-- The dart two steps out of a face along an E-link, used to produce a second
face on a given side of a ring. -/
private theorem diskF_face_edge (hbridge : G.Bridgeless) {r : List D} {u z w : D}
    (hu : G.DiskF r u) (huz : G.CFace u z) (hzw : G.Rlink z w) (hw : ¬ G.Fband r w) :
    G.DiskF r (G.face (G.edge z)) ∧ ¬ G.CFace u (G.face (G.edge z)) := by
  have hz : G.DiskF r z := (diskF_congr huz).mp hu
  refine ⟨⟨diskN_node_iff.mp (by rw [G.edgeK z]; exact hz.1), ?_⟩, ?_⟩
  · rw [fband_face]
    exact fun hc => hw ((Fband.congr hzw).mp hc)
  · intro hc
    have h1 : G.CFace z (G.face (G.edge z)) := huz.symm.trans hc
    exact hbridge z (h1.trans (G.cface_face (G.edge z)).symm)

/-- **A node-simple contract of four darts with a triad admits no contract
ring.**  This is the reference's `triad_valid`. -/
theorem triad_valid (hmin : G.MinimalCounterExample) (hB : G.BirkhoffRings)
    {cc : List D} (hsp : G.Sparse (G.insertE cc)) (hcc4 : cc.length = 4) {x0 : D}
    (htriad : G.Triad (G.insertE cc) x0) (p : List D) : ¬ G.ContractRing cc p := by
  classical
  intro hcr
  have hplan := hmin.planar
  have hplain := hmin.plain
  have hbridge := hmin.bridgeless
  have hcubic := hmin.cubic
  have hconn := hmin.connected
  have hpent := hmin.pentagonal_of_birkhoff hB
  have hnt0 : G.NontrivialRing 0 p :=
    sparse_contract_ring hplan hplain hbridge hcubic hconn hsp hcr
  have hmax := contract_ring_max hplan hplain hcr
  have hlen5 : p.length ≤ 5 := by omega
  -- the ring has exactly five darts
  have hsize : p.length = 5 := by
    by_contra hne
    have hif : (if p.length = 5 then (1 : ℕ) else 0) = 0 := by simp [hne]
    exact hB p hlen5 hcr.scycle (by rw [hif]; exact hnt0)
  have htriv1 : ¬ G.NontrivialRing 1 p := by
    have h := hB p hlen5 hcr.scycle
    have hif : (if p.length = 5 then (1 : ℕ) else 0) = 1 := by simp [hsize]
    rwa [hif] at h
  -- some face has all its neighbours in the band of the ring
  obtain ⟨y0, hy0⟩ : ∃ y0 : D, ∀ y : D, G.Adj y0 y → G.Fband p y := by
    by_contra hcon
    simp only [not_exists] at hcon
    have hne : ∀ y : D, ∃ w, G.Adj y w ∧ ¬ G.Fband p w := by
      intro y
      by_contra hc
      refine hcon y (fun w hw => ?_)
      by_contra hb
      exact hc ⟨w, hw, hb⟩
    obtain ⟨⟨u0, hu0⟩, ⟨u1, hu1⟩⟩ := nontrivialRing_zero_iff.mp hnt0
    refine htriv1 (nontrivialRing_one_iff.mpr ⟨?_, ?_⟩)
    · obtain ⟨w, ⟨z, huz, hzw⟩, hnb⟩ := hne u0
      obtain ⟨h1, h2⟩ := diskF_face_edge hbridge hu0 huz hzw hnb
      exact ⟨u0, G.face (G.edge z), hu0, h1, h2⟩
    · obtain ⟨w, ⟨z, huz, hzw⟩, hnb⟩ := hne u1
      have hz : G.DiskFC p z := (diskFC_congr huz).mp hu1
      refine ⟨u1, G.face (G.edge z), hu1, ⟨?_, ?_⟩, ?_⟩
      · intro hc
        exact hz.1 (by rw [← G.edgeK z]; exact diskN_node_iff.mpr hc)
      · rw [fband_face]
        exact fun hc => hnb ((Fband.congr hzw).mp hc)
      · intro hc
        have h1 : G.CFace z (G.face (G.edge z)) := huz.symm.trans hc
        exact hbridge z (h1.trans (G.cface_face (G.edge z)).symm)
  -- conversely every dart in the band of the ring is adjacent to that face
  have hfba : ∀ z : D, G.Fband p z → G.Adj y0 z := by
    intro z hz
    by_contra hnadj
    have hlt : G.faceCard (G.Fband (G.spokeRing y0)) < G.faceCard (G.Fband p) := by
      refine faceCard_lt_faceCard (fun w hw => hy0 w (fband_spokeRing.mp hw)) hz ?_
      intro w hw hcf
      exact hnadj ((adj_congr_right hcf y0).mp (fband_spokeRing.mp hw))
    rw [faceCard_fband_of_simple (scycle_spokeRing hplan hplain hbridge hcubic hB y0).simple,
      faceCard_fband_of_simple hcr.scycle.simple, length_spokeRing, hsize] at hlt
    have := hpent y0
    omega
  by_cases hout : ∃ u ∈ G.insertE cc, ¬ G.Fband p u
  · -- a contracted dart off the band: one dart of the contract is unused
    obtain ⟨u, hu, hnb⟩ := hout
    obtain ⟨u1, hu1cc, hu1E⟩ := (mem_insertE hplain).mp hu
    obtain ⟨cc1, hcc1⟩ : ∃ cc1, cc.rotate (cc.idxOf u1) = u1 :: cc1 :=
      exists_rotTo_cons hu1cc
    have hcr1 : G.ContractRing cc1 p := by
      refine ⟨hcr.scycle, hcr.proper, fun w hw => ?_⟩
      have hwp : w ∈ p := List.mem_of_mem_tail hw
      obtain ⟨v, hv, hwv⟩ := (mem_insertE hplain).mp (hcr.tail_mem w hw)
      have hv' : v ∈ u1 :: cc1 := by rw [← hcc1]; exact List.mem_rotate.mpr hv
      rcases List.mem_cons.mp hv' with rfl | hv1
      · exfalso
        rcases hplain.cedge_iff.mp (hwv.trans hu1E.symm) with h | h
        · exact hnb (by rw [h]; exact fband_of_mem hwp)
        · refine hnb ⟨p.next w hwp, List.next_mem _ _ _, ?_⟩
          rw [h]
          exact rel_next hcr.scycle.isCyclicChain hcr.scycle.nodup hwp
      · exact (mem_insertE hplain).mpr ⟨v, hv1, hwv⟩
    have hmax1 := contract_ring_max hplan hplain hcr1
    have hlen1 : cc1.length + 1 = cc.length := by
      have h := congrArg List.length hcc1
      simp only [List.length_rotate, List.length_cons] at h
      omega
    omega
  · -- the whole contract lies in the band of the ring
    have hpcc : ∀ u ∈ G.insertE cc, G.Fband p u := by
      intro u hu
      by_contra hb
      exact hout ⟨u, hu, hb⟩
    by_cases hcf : G.CFace x0 y0
    · obtain ⟨v, hv, hnadj⟩ := htriad.not_adj
      exact hnadj ((adj_congr_left hcf v).mpr (hfba v (hpcc v hv)))
    · -- count the faces around `x0` that meet the contract
      have hscy0 := scycle_spokeRing hplan hplain hbridge hcubic hB x0
      have hmaxadj := fcard_adj_max hmin hB (x := x0) (y := y0) hcf
      have hT : ∀ w : D, w ∈ G.spokeRing x0 → G.Fband (G.insertE cc) w →
          G.Adj y0 w ∧ G.Adj x0 w := by
        intro w hw hbw
        obtain ⟨v, hv, hwv⟩ := hbw
        exact ⟨(adj_congr_right hwv y0).mpr (hfba v (hpcc v hv)),
          fband_spokeRing.mp (fband_of_mem hw)⟩
      have hstep2 :
          {w : D | w ∈ G.spokeRing x0 ∧ G.Fband (G.insertE cc) w}.ncard
            ≤ G.faceCard (fun w => G.Adj y0 w ∧ G.Adj x0 w) := by
        refine Set.ncard_le_ncard_of_injOn (Quotient.mk (SameCycle.setoid G.face))
          (fun w hw => ⟨w, hT w hw.1 hw.2, rfl⟩) (fun a ha b hb hab => ?_)
          (Set.toFinite _)
        exact hscy0.simple.eq_of_cface ha.1 hb.1 (Quotient.exact hab)
      have hstep1 : (G.triadSet (G.insertE cc) x0).ncard
          ≤ {w : D | w ∈ G.spokeRing x0 ∧ G.Fband (G.insertE cc) w}.ncard := by
        refine Set.ncard_le_ncard_of_injOn G.spoke (fun y hy => ⟨spoke_mem_spokeRing hy.1, ?_⟩)
          (fun a _ b _ hab => G.spoke_injective hab) (Set.toFinite _)
        rw [spoke, fband_face]
        exact hy.2
      have := htriad.three_le
      omega


/-! ### The double Walkup transform

Contracting the E-link at `x` deletes the two darts `x` and `edge x`.  Both
deletions are `walkupF` transforms, which keep `edge` and `node` and only adjust
`face`: the first merges the face of `x` with the face of `edge x`, and the
second, taken at a dart that has become degenerate, changes nothing. -/

section Walkup

variable [DecidableEq D]

omit [DecidableEq D] in
/-- A dart in a one-dart face is that dart. -/
private theorem eq_of_cface_of_face_fixed {z w : D} (hfz : G.face z = z)
    (h : G.CFace w z) : w = z := by
  obtain ⟨n, hn⟩ := h.symm.exists_nat_pow_eq
  have hfix : ∀ m : ℕ, (G.face ^ m) z = z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Perm.mul_apply, ih, hfz]
  rw [← hn, hfix n]

omit [Finite D] in
/-- The face permutation of `walkupF` is the edge permutation of `walkupE` read
in the `permF` picture. -/
private theorem walkupF_face_eq_permF (G : Hypermap D) (z : D) :
    (G.walkupF z).face = (G.permF.walkupE z).edge := rfl

omit [Finite D] [DecidableEq D] in
/-- Degeneracy is invariant under the `permF` rotation. -/
private theorem glink_self_permF (G : Hypermap D) (z : D) :
    G.permF.GLink z z ↔ G.GLink z z := by
  simp only [GLink, permF_edge, permF_node, permF_face]
  tauto

omit [Finite D] [DecidableEq D] in
/-- In a bridgeless map the only degenerate darts are those in a one-dart
face. -/
private theorem glink_self_iff (hbridge : G.Bridgeless) (z : D) :
    G.GLink z z ↔ G.face z = z := by
  constructor
  · rintro (h | h | h)
    · exact absurd (show G.CFace z (G.edge z) by rw [← h]) (hbridge z)
    · refine absurd ?_ (hbridge z)
      have h0 : G.face (G.edge (G.node z)) = z := G.nodeK z
      rw [← h] at h0
      have h1 : G.CFace (G.edge z) (G.face (G.edge z)) := G.cface_face (G.edge z)
      rw [h0] at h1
      exact h1.symm
    · exact h.symm
  · exact fun h => Or.inr (Or.inr h.symm)

/-- Multiplying by a transposition of two points on distinct orbits merges those
two orbits and leaves every other orbit alone. -/
private theorem sameCycle_swap_mul_of_not (g : Perm D) {a b : D} (hab : a ≠ b)
    (hs : ¬ g.SameCycle a b) (u v : D) :
    (Equiv.swap a b * g).SameCycle u v ↔
      (g.SameCycle u v ∨ (g.SameCycle u a ∧ g.SameCycle v b)
        ∨ (g.SameCycle u b ∧ g.SameCycle v a)) := by
  let _ : Fintype D := Fintype.ofFinite D
  have hswap : (Equiv.swap a b * g).SameCycle a b := (sameCycle_swap_mul_iff g hab).mpr hs
  have hkey : SameCycle.setoid (Equiv.swap a b * g)
      = Setoid.adjoin (SameCycle.setoid g) a b := by
    rw [← Setoid.adjoin_eq_self_of (r := SameCycle.setoid (Equiv.swap a b * g)) hswap]
    exact adjoin_sameCycle_swap_mul g a b
  exact Iff.of_eq (congrArg (fun s : Setoid D => s.r u v) hkey)

/-- At a degenerate dart, `walkupF` does not change the faces. -/
private theorem cface_walkupF_of_glink {z : D} (hz : G.GLink z z) (u v : Walkup G z) :
    (G.walkupF z).CFace u v ↔ G.CFace u.val v.val := by
  change (G.walkupF z).face.SameCycle u v ↔ _
  rw [walkupF_face_eq_permF, walkupE_edge_of_glink G.permF z ((glink_self_permF G z).mpr hz)]
  exact sameCycle_skip G.permF.edge z u v

open scoped Classical in
/-- **The faces of `walkupF`**: deleting `z` merges the face of `z` with the
face of `edge z`, and leaves every other face alone. -/
private theorem cface_walkupF_iff (hbridge : G.Bridgeless) {z : D} (u v : Walkup G z) :
    (G.walkupF z).CFace u v ↔
      (if G.CFace u.val z ∨ G.CFace u.val (G.edge z)
        then G.CFace v.val z ∨ G.CFace v.val (G.edge z)
        else G.CFace u.val v.val) := by
  classical
  by_cases hz : G.GLink z z
  · -- the degenerate case: the face of `z` is a single dart
    have hfz : G.face z = z := (glink_self_iff hbridge z).mp hz
    have hmain : (G.walkupF z).CFace u v ↔ G.CFace u.val v.val := by
      change (G.walkupF z).face.SameCycle u v ↔ _
      rw [walkupF_face_eq_permF,
        walkupE_edge_of_glink G.permF z ((glink_self_permF G z).mpr hz)]
      exact sameCycle_skip G.permF.edge z u v
    have hzu : ∀ w : Walkup G z, ¬ G.CFace w.val z := fun w hw =>
      w.2 (eq_of_cface_of_face_fixed hfz hw)
    rw [hmain]
    split
    · rename_i hcond
      have hc : G.CFace u.val (G.edge z) := hcond.resolve_left (hzu u)
      exact ⟨fun huv => Or.inr (huv.symm.trans hc),
        fun hv => hc.trans (hv.resolve_left (hzu v)).symm⟩
    · exact Iff.rfl
  · -- the generic case: the faces of `z` and of `edge z` merge
    let _ : Fintype D := Fintype.ofFinite D
    have hzp : ¬ G.permF.GLink z z := fun hc => hz ((glink_self_permF G z).mp hc)
    have hmain : (G.walkupF z).CFace u v ↔
        (G.CFace u.val v.val
          ∨ (G.CFace u.val z ∧ G.CFace v.val (G.edge z))
          ∨ (G.CFace u.val (G.edge z) ∧ G.CFace v.val z)) := by
      change (G.walkupF z).face.SameCycle u v ↔ _
      rw [walkupF_face_eq_permF, walkupE_edge_eq_swap_mul G.permF z hzp,
        sameCycle_swap_mul_of_not _ (edge_ne_edge_node_of_not_glink G.permF z hzp)
          (fun hc => hbridge z ((sameCycle_skip_edge_swap_iff G.permF z hzp).mp hc)) u v]
      simp only [sameCycle_skip, permF_edge, permF_node, sameCycle_apply_right]
    rw [hmain]
    split
    · rename_i hcond
      constructor
      · rintro (huv | ⟨-, h2⟩ | ⟨-, h2⟩)
        · rcases hcond with h | h
          · exact Or.inl (huv.symm.trans h)
          · exact Or.inr (huv.symm.trans h)
        · exact Or.inr h2
        · exact Or.inl h2
      · rintro (hv | hv)
        · rcases hcond with h | h
          · exact Or.inl (h.trans hv.symm)
          · exact Or.inr (Or.inr ⟨h, hv⟩)
        · rcases hcond with h | h
          · exact Or.inr (Or.inl ⟨h, hv⟩)
          · exact Or.inl (h.trans hv.symm)
    · rename_i hcond
      constructor
      · rintro (huv | ⟨h1, -⟩ | ⟨h1, -⟩)
        · exact huv
        · exact absurd (Or.inl h1) hcond
        · exact absurd (Or.inr h1) hcond
      · exact Or.inl

/-! ### List helpers for the contraction argument -/

section ListHelpers

variable {α β : Type*}

/-- A failing chain has an adjacent pair that is not linked. -/
private theorem exists_break_of_not_isChain {R : α → α → Prop} :
    ∀ {l : List α}, ¬ List.IsChain R l →
      ∃ (u v : α) (s t : List α), l = s ++ u :: v :: t ∧ ¬ R u v := by
  intro l
  induction l with
  | nil => exact fun h => absurd List.IsChain.nil h
  | cons a l ih =>
    rcases l with _ | ⟨b, t⟩
    · exact fun h => absurd (List.IsChain.singleton a) h
    · intro h
      by_cases hab : R a b
      · obtain ⟨u, v, s, t', hs, hR⟩ := ih fun hc => h (List.isChain_cons_cons.mpr ⟨hab, hc⟩)
        exact ⟨u, v, a :: s, t', by rw [hs]; rfl, hR⟩
      · exact ⟨a, b, [], t, rfl, hab⟩

/-- Weakening a chain, using a property of all but the first dart. -/
private theorem isChain_imp_of_tail {R S : α → α → Prop} {P : α → Prop}
    (hstep : ∀ a b, P b → R a b → S a b) :
    ∀ {l : List α}, (∀ b ∈ l.tail, P b) → List.IsChain R l → List.IsChain S l
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.IsChain.singleton a
  | _ :: b :: _, hP, h => by
      rw [List.isChain_cons_cons] at h ⊢
      exact ⟨hstep _ b (hP b List.mem_cons_self) h.1,
        isChain_imp_of_tail hstep (fun c hc => hP c (List.mem_cons_of_mem _ hc)) h.2⟩

/-- The last dart of a mapped list, with a fallback. -/
private theorem getLastD_map (f : α → β) :
    ∀ (l : List α) (d : α), (l.map f).getLastD (f d) = f (l.getLastD d)
  | [], _ => rfl
  | a :: t, d => by
      rw [List.map_cons, List.getLastD_cons, List.getLastD_cons]
      exact getLastD_map f t a

/-- The last dart of a mapped list with a head, with a fallback. -/
private theorem getLastD_map_cons (f : α → β) (d : β) (a : α) (l : List α) :
    ((a :: l).map f).getLastD d = f (l.getLastD a) := by
  rw [List.map_cons, List.getLastD_cons]
  exact getLastD_map f l a

/-- The last dart of a mapped list with a head. -/
private theorem getLast_map_cons (f : α → β) (a : α) (l : List α) :
    ((a :: l).map f).getLast (by simp) = f (l.getLastD a) :=
  getLastD_map_cons f (f a) a l

/-- The last dart of a mapped list with a head, after one more dart. -/
private theorem getLast_cons_map_cons (f : α → β) (d : β) (a : α) (l : List α) :
    (d :: ((a :: l).map f)).getLast (by simp) = f (l.getLastD a) := by
  have h1 : (d :: ((a :: l).map f)).getLast (by simp)
      = ((a :: l).map f).getLastD d :=
    List.getLastD_cons (a := d) (b := d) (l := (a :: l).map f)
  rw [h1, getLastD_map_cons]

/-- The last dart of a list with a head that ends in a given dart. -/
private theorem getLast_cons_concat :
    ∀ (a : α) (l : List α) (b : α), (a :: (l ++ [b])).getLast (List.cons_ne_nil _ _) = b
  | _, [], _ => rfl
  | _, c :: l, b => by
      rw [List.cons_append, List.getLast_cons_cons]
      exact getLast_cons_concat c l b

end ListHelpers

/-! ### The double transform at an E-link -/

section DoubleWalkup

variable {x : D} {uex : Walkup G x}

omit [Finite D] in
/-- Two darts of the double transform with the same underlying dart are
equal. -/
private theorem eq_of_val_val {a b : Walkup (G.walkupF x) uex}
    (h : a.val.val = b.val.val) : a = b := Subtype.ext (Subtype.ext h)

omit [Finite D] in
/-- The darts of the double transform are the darts off the E-link at `x`. -/
private theorem val_val_ne (huex : uex.val = G.edge x) (w : Walkup (G.walkupF x) uex) :
    w.val.val ≠ x ∧ w.val.val ≠ G.edge x :=
  ⟨w.val.2, fun hc => w.2 (Subtype.ext (hc.trans huex.symm))⟩

omit [Finite D] in
/-- Every dart off the E-link at `x` is a dart of the double transform. -/
private theorem exists_val_val (huex : uex.val = G.edge x) {y : D} (hy : y ≠ x)
    (hey : y ≠ G.edge x) : ∃ w : Walkup (G.walkupF x) uex, w.val.val = y :=
  ⟨⟨⟨y, hy⟩, fun hc => hey ((congrArg Subtype.val hc).trans huex)⟩, rfl⟩

/-- The double transform does not change which darts share a node. -/
private theorem cnode_walkup2 (w w' : Walkup (G.walkupF x) uex) :
    ((G.walkupF x).walkupF uex).CNode w w' ↔ G.CNode w.val.val w'.val.val :=
  (sameCycle_skip (skip G.node x) uex w w').trans (sameCycle_skip G.node x w.val w'.val)

/-- The double transform does not change which darts share an edge. -/
private theorem cedge_walkup2 (w w' : Walkup (G.walkupF x) uex) :
    ((G.walkupF x).walkupF uex).CEdge w w' ↔ G.CEdge w.val.val w'.val.val :=
  (sameCycle_skip (skip G.edge x) uex w w').trans (sameCycle_skip G.edge x w.val w'.val)

omit [Finite D] in
/-- The double transform commutes with `edge`. -/
private theorem edge_walkup2 (hplain : G.Plain) (huex : uex.val = G.edge x)
    (w : Walkup (G.walkupF x) uex) :
    (((G.walkupF x).walkupF uex).edge w).val.val = G.edge w.val.val := by
  obtain ⟨hx1, hx2⟩ := val_val_ne huex w
  have h1 : G.edge w.val.val ≠ x := fun hc =>
    hx2 (by rw [← hplain.edge_edge w.val.val, hc])
  have hinner : ((G.walkupF x).edge w.val).val = G.edge w.val.val := skip_val_of_ne h1
  have h2 : (G.walkupF x).edge w.val ≠ uex := by
    intro hc
    refine hx1 (G.edge.injective ?_)
    rw [← hinner, hc, huex]
  have hout : (((G.walkupF x).walkupF uex).edge w).val = (G.walkupF x).edge w.val :=
    skip_val_of_ne h2
  rw [hout, hinner]

omit [Finite D] in
/-- The double transform is plain. -/
private theorem plain_walkup2 (hplain : G.Plain) (huex : uex.val = G.edge x) :
    ((G.walkupF x).walkupF uex).Plain := by
  refine ⟨fun w => eq_of_val_val ?_, fun w hc => ?_⟩
  · rw [edge_walkup2 hplain huex, edge_walkup2 hplain huex, hplain.edge_edge]
  · exact hplain.edge_ne w.val.val (by rw [← edge_walkup2 hplain huex, hc])

/-- The double transform is precubic. -/
private theorem precubic_walkup2 (hprecubic : G.Precubic) :
    ((G.walkupF x).walkupF uex).Precubic := by
  intro w
  have hsub : (orbitList ((G.walkupF x).walkupF uex).node w).map
      (fun v : Walkup (G.walkupF x) uex => v.val.val) ⊆ orbitList G.node w.val.val := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact mem_orbitList.mpr ((cnode_walkup2 w v).mp (mem_orbitList.mp hv))
  have hnd : ((orbitList ((G.walkupF x).walkupF uex).node w).map
      (fun v : Walkup (G.walkupF x) uex => v.val.val)).Nodup :=
    List.Nodup.map_on (fun a _ b _ hab => eq_of_val_val hab)
      (nodup_orbitList ((G.walkupF x).walkupF uex).node w)
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_map, length_orbitList] at hle
  exact le_trans hle (hprecubic w.val.val)

open scoped Classical in
/-- **The faces of the double transform**: the face of `x` and the face of
`edge x` have merged into one, and no other face has changed. -/
private theorem cface_walkup2 (hplain : G.Plain) (hbridge : G.Bridgeless)
    (huex : uex.val = G.edge x) (w w' : Walkup (G.walkupF x) uex) :
    ((G.walkupF x).walkupF uex).CFace w w' ↔
      (if G.CFace w.val.val x ∨ G.CFace w.val.val (G.edge x)
        then G.CFace w'.val.val x ∨ G.CFace w'.val.val (G.edge x)
        else G.CFace w.val.val w'.val.val) := by
  classical
  have hglink : (G.walkupF x).GLink uex uex := by
    refine Or.inl (Subtype.ext ?_).symm
    have h1 : G.edge uex.val = x := by rw [huex, hplain.edge_edge]
    have h2 : ((skip G.edge x) uex).val = G.edge x := skip_val_of_eq h1
    rw [show ((G.walkupF x).edge uex) = (skip G.edge x) uex from rfl, h2, huex]
  exact (cface_walkupF_of_glink hglink w w').trans (cface_walkupF_iff hbridge w.val w'.val)


/-! ### Contract rings and contract colourings across the double transform -/

section Contraction

variable {x : D} {uex : Walkup G x} {cc : List D} {cc2 : List (Walkup (G.walkupF x) uex)}

open scoped Classical in
/-- Faces of the original map lift to faces of the double transform. -/
private theorem cface_lift (hplain : G.Plain) (hbridge : G.Bridgeless)
    (huex : uex.val = G.edge x) (a b : Walkup (G.walkupF x) uex)
    (hab : G.CFace a.val.val b.val.val) : ((G.walkupF x).walkupF uex).CFace a b := by
  rw [cface_walkup2 hplain hbridge huex a b]
  split
  · rename_i hcond
    rcases hcond with h | h
    · exact Or.inl (hab.symm.trans h)
    · exact Or.inr (hab.symm.trans h)
  · exact hab

open scoped Classical in
/-- An R-link of the double transform whose target is off the merged face is an
R-link of the original map. -/
private theorem rlink_of_rlink_walkup2 (hplain : G.Plain) (hbridge : G.Bridgeless)
    (huex : uex.val = G.edge x) (a b : Walkup (G.walkupF x) uex)
    (hnb : ¬ (G.CFace b.val.val x ∨ G.CFace b.val.val (G.edge x)))
    (hab : ((G.walkupF x).walkupF uex).Rlink a b) : G.Rlink a.val.val b.val.val := by
  have hab' : ((G.walkupF x).walkupF uex).CFace
      (((G.walkupF x).walkupF uex).edge a) b := hab
  rw [cface_walkup2 hplain hbridge huex _ b, edge_walkup2 hplain huex a] at hab'
  split at hab'
  · exact absurd hab' hnb
  · exact hab'

open scoped Classical in
/-- **The double transform inherits the absence of contract rings.** -/
private theorem no_contractRing_walkup2 (hplain : G.Plain)
    (hbridge : G.Bridgeless) (huex : uex.val = G.edge x)
    (hEcc : ∀ w : Walkup (G.walkupF x) uex,
      w ∈ ((G.walkupF x).walkupF uex).insertE cc2 ↔ w.val.val ∈ G.insertE (x :: cc))
    (hno : ∀ q, ¬ G.ContractRing (x :: cc) q) :
    ∀ q, ¬ ((G.walkupF x).walkupF uex).ContractRing cc2 q := by
  classical
  intro p hp
  have hF := cface_walkup2 hplain hbridge huex
  have h_e := edge_walkup2 hplain huex
  have hscyc := hp.scycle
  have hproper := hp.proper
  have htail := hp.tail_mem
  obtain ⟨w, p0, rfl⟩ : ∃ w p0, p = w :: p0 := by
    rcases p with _ | ⟨w, p0⟩
    · exact hproper.elim
    · exact ⟨w, p0, rfl⟩
  -- the projected ring is face-simple, properly closed and contracted
  have hsimple : G.Simple ((w :: p0).map (fun v : Walkup (G.walkupF x) uex => v.val.val)) :=
    List.pairwise_map.mpr
      (hscyc.simple.imp fun {a b} hab hc => hab (cface_lift hplain hbridge huex a b hc))
  have htailimg : ∀ y ∈ ((w :: p0).map
      (fun v : Walkup (G.walkupF x) uex => v.val.val)).tail, y ∈ G.insertE (x :: cc) := by
    intro y hy
    simp only [List.map_cons, List.tail_cons] at hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact (hEcc v).mp (htail v hv)
  have hproperimg : G.ProperRing ((w :: p0).map
      (fun v : Walkup (G.walkupF x) uex => v.val.val)) := by
    rcases p0 with _ | ⟨b, t⟩
    · exact hproper.elim
    · rcases t with _ | ⟨c, t'⟩
      · simp only [List.map_cons, List.map_nil]
        rw [properRing_pair] at hproper ⊢
        intro hc
        exact hproper (eq_of_val_val (by rw [h_e w]; exact hc))
      · refine G.properRing_of_two_lt_length ?_
        simp only [List.length_map, List.length_cons]
        omega
  by_cases hcyc : IsCyclicChain G.Rlink ((w :: p0).map
      (fun v : Walkup (G.walkupF x) uex => v.val.val))
  · exact hno _ ⟨⟨hcyc, hsimple⟩, hproperimg, htailimg⟩
  -- otherwise a cyclic step of the ring is broken by the contraction
  obtain ⟨n, w1, p1, hp', hbad⟩ :
      ∃ (n : ℕ) (w1 : Walkup (G.walkupF x) uex) (p1 : List (Walkup (G.walkupF x) uex)),
        (w :: p0).rotate n = w1 :: p1 ∧
        ¬ G.Rlink ((w1 :: p1).getLast (List.cons_ne_nil w1 p1)).val.val w1.val.val := by
    by_cases hch : List.IsChain (fun a b : Walkup (G.walkupF x) uex =>
        G.Rlink a.val.val b.val.val) (w :: p0)
    · refine ⟨0, w, p0, List.rotate_zero _, fun hwrap => hcyc ?_⟩
      rw [getLast_cons_eq_getLastD] at hwrap
      have hch' : List.IsChain G.Rlink ((w :: p0).map
          (fun v : Walkup (G.walkupF x) uex => v.val.val)) :=
        (List.isChain_map (l := w :: p0) _).mpr hch
      refine isCyclicChain_cons.mpr ⟨hch', ?_⟩
      have hlast : ((w :: p0).map (fun v : Walkup (G.walkupF x) uex => v.val.val)).getLast
          (by simp) = (p0.getLastD w).val.val := getLast_map_cons _ w p0
      rw [← hlast] at hwrap
      exact hwrap
    · obtain ⟨u, v, s, t, hst, hR⟩ := exists_break_of_not_isChain hch
      refine ⟨s.length + 1, v, t ++ s ++ [u], ?_, ?_⟩
      · rw [hst, show s ++ u :: v :: t = (s ++ [u]) ++ (v :: t) by simp,
          show s.length + 1 = (s ++ [u]).length by simp, List.rotate_append_length_eq]
        simp
      · rw [getLast_cons_concat]
        exact hR
  -- the rotation of the ring that starts just after the broken step
  have hcycp' : IsCyclicChain ((G.walkupF x).walkupF uex).Rlink (w1 :: p1) := by
    rw [← hp']
    exact isCyclicChain_rotate.mpr hscyc.isCyclicChain
  have hsimplep' : ((G.walkupF x).walkupF uex).Simple (w1 :: p1) := by
    rw [← hp']
    exact simple_rotate.mpr hscyc.simple
  obtain ⟨hchainp', hwrap⟩ := isCyclicChain_cons.mp hcycp'
  obtain ⟨hband1, hsimp1⟩ := simple_cons.mp hsimplep'
  set w0 : Walkup (G.walkupF x) uex := (w1 :: p1).getLast (List.cons_ne_nil w1 p1) with hw0
  have hgood' : ((G.walkupF x).walkupF uex).CFace
      (((G.walkupF x).walkupF uex).edge w0) w1 := hwrap
  rw [hF _ w1, h_e w0] at hgood'
  obtain ⟨hdom0, hdom1⟩ :
      (G.CFace (G.edge w0.val.val) x ∨ G.CFace (G.edge w0.val.val) (G.edge x))
        ∧ (G.CFace w1.val.val x ∨ G.CFace w1.val.val (G.edge x)) := by
    split at hgood'
    · rename_i hcond
      exact ⟨hcond, hgood'⟩
    · exact absurd hgood' hbad
  -- the darts of the E-link at `x` that the two ends meet
  obtain ⟨x0, hx0mem, hx0⟩ : ∃ x0, (x0 = x ∨ x0 = G.edge x)
      ∧ G.CFace (G.edge w0.val.val) x0 :=
    hdom0.elim (fun h => ⟨x, Or.inl rfl, h⟩) (fun h => ⟨G.edge x, Or.inr rfl, h⟩)
  obtain ⟨x1, hx1mem, hx1⟩ : ∃ x1, (x1 = x ∨ x1 = G.edge x) ∧ G.CFace w1.val.val x1 :=
    hdom1.elim (fun h => ⟨x, Or.inl rfl, h⟩) (fun h => ⟨G.edge x, Or.inr rfl, h⟩)
  have hx01 : G.edge x0 = x1 := by
    rcases hx0mem with h0 | h0 <;> rcases hx1mem with h1 | h1
    · refine absurd ?_ hbad
      rw [h0] at hx0
      rw [h1] at hx1
      exact hx0.trans hx1.symm
    · rw [h0, h1]
    · rw [h0, h1, hplain.edge_edge]
    · refine absurd ?_ hbad
      rw [h0] at hx0
      rw [h1] at hx1
      exact hx0.trans hx1.symm
  -- no other dart of the ring meets the merged face
  have hnodom : ∀ v ∈ p1, ¬ (G.CFace v.val.val x ∨ G.CFace v.val.val (G.edge x)) := by
    intro v hv hdv
    refine hband1 ⟨v, hv, ?_⟩
    rw [hF w1 v]
    split
    · exact hdv
    · rename_i hcond
      exact absurd hdom1 hcond
  have hchainkey : List.IsChain (fun a b : Walkup (G.walkupF x) uex =>
      G.Rlink a.val.val b.val.val) (w1 :: p1) := by
    refine isChain_imp_of_tail
      (fun a b hb hab => rlink_of_rlink_walkup2 hplain hbridge huex a b hb hab) ?_ hchainp'
    simpa using hnodom
  have hchainimg : List.IsChain G.Rlink (w1.val.val ::
      p1.map (fun v : Walkup (G.walkupF x) uex => v.val.val)) :=
    (List.isChain_map (l := w1 :: p1) _).mpr hchainkey
  -- the repaired ring
  set q1 : List D :=
    x0 :: ((w1 :: p1).map (fun v : Walkup (G.walkupF x) uex => v.val.val)) with hq1
  have hw0eq : w0 = p1.getLastD w1 := hw0.trans (getLast_cons_eq_getLastD w1 p1)
  have hcycq1 : IsCyclicChain G.Rlink q1 := by
    rw [hq1]
    refine isCyclicChain_cons.mpr ⟨?_, ?_⟩
    · rw [List.map_cons]
      refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
      · change G.CFace (G.edge x0) w1.val.val
        rw [hx01]
        exact hx1.symm
      · exact hchainimg
    · have hlast2 : (x0 :: ((w1 :: p1).map
          (fun v : Walkup (G.walkupF x) uex => v.val.val))).getLast (by simp)
            = w0.val.val := by
        rw [hw0eq]
        exact getLast_cons_map_cons _ x0 w1 p1
      rw [hlast2]
      exact hx0
  have hsimpleq1 : G.Simple q1 := by
    rw [hq1]
    refine simple_cons.mpr ⟨?_, ?_⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_cons.mp hv with h1 | hv'
      · rw [h1] at hxy
        exact hbridge x0 (by rw [hx01]; exact hxy.trans hx1)
      · refine hnodom v hv' ?_
        rcases hx0mem with h0 | h0
        · exact Or.inl (h0 ▸ hxy.symm)
        · exact Or.inr (h0 ▸ hxy.symm)
    · exact List.pairwise_map.mpr
        (hsimplep'.imp fun {a b} hab hc => hab (cface_lift hplain hbridge huex a b hc))
  -- rotate the repaired ring to start at the head of the original one
  have hwq1 : w.val.val ∈ q1 := by
    rw [hq1]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, ?_, rfl⟩)
    rw [← hp']
    exact List.mem_rotate.mpr List.mem_cons_self
  obtain ⟨sq, hsq⟩ := exists_rotTo_cons hwq1
  have hrotq : q1.rotate (q1.idxOf (w.val.val)) = w.val.val :: sq := hsq
  have hnd : (w.val.val :: sq).Nodup := by
    rw [← hrotq]
    exact (simple_rotate.mpr hsimpleq1).nodup
  have hp0ne : p0 ≠ [] := by rintro rfl; exact hproper.elim
  have hlen1 : p1.length = p0.length := by
    have h := congrArg List.length hp'
    simp only [List.length_rotate, List.length_cons] at h
    omega
  refine hno (w.val.val :: sq) ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← hrotq]
    exact isCyclicChain_rotate.mpr hcycq1
  · rw [← hrotq]
    exact simple_rotate.mpr hsimpleq1
  · refine G.properRing_of_two_lt_length ?_
    have h1 : (w.val.val :: sq).length = q1.length := by
      rw [← hrotq, List.length_rotate]
    have h3 : 0 < p0.length := List.length_pos_iff.mpr hp0ne
    rw [h1, hq1]
    simp only [List.length_cons, List.length_map]
    omega
  · intro y hy
    have hyq1 : y ∈ q1 := by
      rw [← List.mem_rotate (n := q1.idxOf (w.val.val)), hrotq]
      exact List.mem_cons_of_mem _ hy
    have hyne : y ≠ w.val.val := by
      intro hc
      rw [hc] at hy
      exact (List.nodup_cons.mp hnd).1 hy
    rw [hq1] at hyq1
    rcases List.mem_cons.mp hyq1 with h0 | hy'
    · rw [h0]
      rcases hx0mem with h1 | h1 <;> rw [h1] <;> simp
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy'
      have hvp : v ∈ w :: p0 := by
        rw [← List.mem_rotate (n := n), hp']
        exact hv
      rcases List.mem_cons.mp hvp with h1 | hv'
      · exact absurd (congrArg (fun u : Walkup (G.walkupF x) uex => u.val.val) h1) hyne
      · exact (hEcc v).mp (htail v hv')

open scoped Classical in
/-- A dart whose face misses the double transform lies on the E-link at `x` and
has a one-dart face. -/
private theorem face_eq_self_of_no_lift (hplain : G.Plain) (hbridge : G.Bridgeless)
    (huex : uex.val = G.edge x) (y : D) :
    (¬ ∃ w : Walkup (G.walkupF x) uex, G.CFace y w.val.val)
      ↔ (G.face y = y ∧ (y = x ∨ y = G.edge x)) := by
  classical
  constructor
  · intro hy
    have hy1 : y = x ∨ y = G.edge x := by
      by_contra hc1
      push Not at hc1
      obtain ⟨w, hw⟩ := exists_val_val huex hc1.1 hc1.2
      exact hy ⟨w, by rw [hw]⟩
    have hy2 : G.face y = x ∨ G.face y = G.edge x := by
      by_contra hc1
      push Not at hc1
      obtain ⟨w, hw⟩ := exists_val_val huex hc1.1 hc1.2
      exact hy ⟨w, by rw [hw]; exact G.cface_face y⟩
    refine ⟨?_, hy1⟩
    by_contra hfy
    have hfe : G.face y = G.edge y := by
      rcases hy1 with h1 | h1
      · rw [h1] at hy2 hfy ⊢
        exact hy2.resolve_left hfy
      · rw [h1] at hy2 hfy ⊢
        rw [hplain.edge_edge]
        exact hy2.resolve_right hfy
    exact hbridge y (by rw [← hfe]; exact G.cface_face y)
  · rintro ⟨hfy, hy1⟩ ⟨w, hw⟩
    have hval := eq_of_cface_of_face_fixed hfy hw.symm
    rcases hy1 with h1 | h1
    · exact (val_val_ne huex w).1 (hval.trans h1)
    · exact (val_val_ne huex w).2 (hval.trans h1)

omit [DecidableEq D] in
/-- In a plain bridgeless precubic map, a one-dart face has a one-dart face
across its E-link. -/
private theorem face_edge_eq_of_face_eq (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hprecubic : G.Precubic) {z : D} (hfz : G.face z = z) :
    G.face (G.edge z) = G.edge z := by
  have h1 : G.edge (G.node z) = z :=
    G.face.injective ((G.nodeK z).trans hfz.symm)
  have hnz : G.node z = G.edge z := by
    have h2 := congrArg (G.edge : D → D) h1
    rwa [hplain.edge_edge] at h2
  have hnn : G.node (G.node z) = z := by
    have hp3 : Function.minimalPeriod G.node z ≤ 3 := hprecubic z
    have hppos : 0 < Function.minimalPeriod G.node z :=
      Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts G.node z)
    have hne1 : Function.minimalPeriod G.node z ≠ 1 := by
      intro hc
      have h4 : G.node z = z := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hc
      rw [hnz] at h4
      exact hplain.edge_ne z h4
    have hne3 : Function.minimalPeriod G.node z ≠ 3 := by
      intro hc
      have h3 : G.node (G.node (G.node z)) = z := by
        have h0 := Function.iterate_minimalPeriod (f := (G.node : D → D)) (x := z)
        rw [hc] at h0
        exact h0
      have e1 : G.face (G.edge (G.node (G.node z))) = G.node z := G.nodeK (G.node z)
      have e2 : G.face (G.edge z) = G.node (G.node z) := by
        have h5 := G.nodeK (G.node (G.node z))
        rw [h3] at h5
        exact h5
      have e3 : G.face (G.face (G.edge (G.node (G.node z)))) = G.node (G.node z) := by
        rw [e1]
        conv_lhs => rw [hnz]
        exact e2
      refine hbridge (G.node (G.node z)) ?_
      have h4 : G.CFace (G.edge (G.node (G.node z)))
          (G.face (G.face (G.edge (G.node (G.node z))))) :=
        (G.cface_face _).trans (G.cface_face _)
      rw [e3] at h4
      exact h4.symm
    have hmp2 : Function.minimalPeriod G.node z = 2 := by omega
    have h0 := Function.iterate_minimalPeriod (f := (G.node : D → D)) (x := z)
    rw [hmp2] at h0
    exact h0
  have h2 : G.face (G.edge (G.node (G.node z))) = G.node z := G.nodeK (G.node z)
  rw [hnn, hnz] at h2
  exact h2

open scoped Classical in
/-- **Transporting a contract colouring back across the double transform.** -/
private theorem ccColorable_of_walkup2 (hplain : G.Plain) (hbridge : G.Bridgeless)
    (hprecubic : G.Precubic) (huex : uex.val = G.edge x)
    (hEcc : ∀ w : Walkup (G.walkupF x) uex,
      w ∈ ((G.walkupF x).walkupF uex).insertE cc2 ↔ w.val.val ∈ G.insertE (x :: cc))
    (hcol : ((G.walkupF x).walkupF uex).CcColorable cc2) : G.CcColorable (x :: cc) := by
  classical
  obtain ⟨k, hk⟩ := hcol
  have hF := cface_walkup2 hplain hbridge huex
  have h_e := edge_walkup2 hplain huex
  have hempty := face_eq_self_of_no_lift hplain hbridge huex
  obtain ⟨k0, hk0def⟩ : ∃ k0 : D → Color, ∀ y : D, k0 y =
      if hy : ∃ w : Walkup (G.walkupF x) uex, G.CFace y w.val.val
      then k hy.choose else Color.c0 := ⟨_, fun _ => rfl⟩
  have hk0 : ∀ (y : D) (w : Walkup (G.walkupF x) uex), G.CFace y w.val.val → k0 y = k w := by
    intro y w hyw
    rw [hk0def y]
    split
    · rename_i hy
      exact hk.cface (cface_lift hplain hbridge huex _ _ (hy.choose_spec.symm.trans hyw))
    · rename_i hy
      exact absurd ⟨w, hyw⟩ hy
  have hk0h : ∀ w : Walkup (G.walkupF x) uex, k0 w.val.val = k w :=
    fun w => hk0 _ w (SameCycle.refl _ _)
  -- the two darts of the contracted E-link get the same colour
  have haex : (¬ ∃ w : Walkup (G.walkupF x) uex, G.CFace x w.val.val)
      ↔ (¬ ∃ w : Walkup (G.walkupF x) uex, G.CFace (G.edge x) w.val.val) := by
    rw [hempty, hempty]
    constructor
    · rintro ⟨hf, -⟩
      exact ⟨face_edge_eq_of_face_eq hplain hbridge hprecubic hf, Or.inr rfl⟩
    · rintro ⟨hf, -⟩
      have h1 := face_edge_eq_of_face_eq hplain hbridge hprecubic hf
      rw [hplain.edge_edge] at h1
      exact ⟨h1, Or.inl rfl⟩
  have hk0ex : k0 x = k0 (G.edge x) := by
    by_cases hx : ∃ w : Walkup (G.walkupF x) uex, G.CFace x w.val.val
    · obtain ⟨w, hw⟩ := hx
      obtain ⟨w', hw'⟩ : ∃ w' : Walkup (G.walkupF x) uex, G.CFace (G.edge x) w'.val.val := by
        by_contra hcc
        exact haex.mpr hcc ⟨w, hw⟩
      rw [hk0 x w hw, hk0 (G.edge x) w' hw']
      refine hk.cface ?_
      rw [hF w w']
      split
      · exact Or.inr hw'.symm
      · rename_i hcond
        exact absurd (Or.inl hw.symm) hcond
    · have hx' := haex.mp hx
      have h1 : k0 x = Color.c0 := by
        rw [hk0def x]
        split
        · rename_i hcond
          exact absurd hcond hx
        · rfl
      have h2 : k0 (G.edge x) = Color.c0 := by
        rw [hk0def (G.edge x)]
        split
        · rename_i hcond
          exact absurd hcond hx'
        · rfl
      rw [h1, h2]
  refine ⟨k0, fun y => ?_, fun y => ?_⟩
  · by_cases hxy : G.CEdge x y
    · have hmem : y ∈ G.insertE (x :: cc) := by
        rcases hplain.cedge_iff.mp hxy with h | h <;> rw [h] <;> simp
      refine iff_of_true ?_ hmem
      rcases hplain.cedge_iff.mp hxy with h | h
      · rw [h]
        exact hk0ex.symm
      · rw [h, hplain.edge_edge]
        exact hk0ex
    · obtain ⟨w, rfl⟩ : ∃ w : Walkup (G.walkupF x) uex, w.val.val = y := by
        refine exists_val_val huex (fun hc => hxy ?_) (fun hc => hxy ?_)
        · rw [hc]
        · rw [hc]
          exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
      rw [← h_e w, hk0h, hk0h, hk.edge w, hEcc w]
  · by_cases hy : ∃ w : Walkup (G.walkupF x) uex, G.CFace y w.val.val
    · obtain ⟨w, hw⟩ := hy
      rw [hk0 (G.face y) w ((G.cface_face y).symm.trans hw), hk0 y w hw]
    · have h1 : k0 (G.face y) = Color.c0 := by
        rw [hk0def (G.face y)]
        split
        · rename_i hcc
          obtain ⟨w, hw⟩ := hcc
          exact absurd ⟨w, (G.cface_face y).trans hw⟩ hy
        · rfl
      have h2 : k0 y = Color.c0 := by
        rw [hk0def y]
        split
        · rename_i hcc
          exact absurd hcc hy
        · rfl
      rw [h1, h2]

omit [Finite D] [DecidableEq D] in
/-- A two-dart cyclic chain. -/
private theorem isCyclicChain_pair {e : D → D → Prop} {a b : D} (h1 : e a b) (h2 : e b a) :
    IsCyclicChain e [a, b] :=
  isCyclicChain_cons.mpr ⟨List.isChain_cons_cons.mpr ⟨h1, List.IsChain.singleton b⟩, h2⟩

open scoped Classical in
/-- **The double transform is bridgeless**, as soon as the contract admits no
two-dart contract ring. -/
private theorem bridgeless_walkup2 (hplain : G.Plain) (hbridge : G.Bridgeless)
    (huex : uex.val = G.edge x) (hno : ∀ q, ¬ G.ContractRing (x :: cc) q) :
    ((G.walkupF x).walkupF uex).Bridgeless := by
  classical
  intro w hw
  have hw' : ((G.walkupF x).walkupF uex).CFace w
      (((G.walkupF x).walkupF uex).edge w) := hw
  rw [cface_walkup2 hplain hbridge huex w _, edge_walkup2 hplain huex w] at hw'
  obtain ⟨hdom, hdom'⟩ :
      (G.CFace w.val.val x ∨ G.CFace w.val.val (G.edge x))
        ∧ (G.CFace (G.edge w.val.val) x ∨ G.CFace (G.edge w.val.val) (G.edge x)) := by
    split at hw'
    · rename_i hcond
      exact ⟨hcond, hw'⟩
    · exact absurd hw' (hbridge w.val.val)
  obtain ⟨y, hxy, hay, hya⟩ : ∃ y : D, G.CEdge x y
      ∧ G.Rlink w.val.val y ∧ G.Rlink y w.val.val := by
    rcases hdom with h1 | h1
    · refine ⟨G.edge x, sameCycle_apply_right.mpr (SameCycle.refl _ _), ?_, ?_⟩
      · exact hdom'.resolve_left fun h2 => hbridge w.val.val (h1.trans h2.symm)
      · change G.CFace (G.edge (G.edge x)) w.val.val
        rw [hplain.edge_edge]
        exact h1.symm
    · refine ⟨x, SameCycle.refl _ _, ?_, ?_⟩
      · exact hdom'.resolve_right fun h2 => hbridge w.val.val (h1.trans h2.symm)
      · exact h1.symm
  have hxEa : ¬ G.CEdge x w.val.val := by
    intro hc
    rcases hplain.cedge_iff.mp hc with h | h
    · exact (val_val_ne huex w).1 h
    · exact (val_val_ne huex w).2 h
  refine hno [w.val.val, y] ⟨⟨isCyclicChain_pair hay hya, ?_⟩, ?_, ?_⟩
  · refine simple_cons.mpr ⟨?_, simple_cons.mpr ⟨fband_nil y, simple_nil⟩⟩
    rintro ⟨z, hz, hcz⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact hbridge w.val.val (hcz.trans hay.symm)
  · rw [properRing_pair]
    intro hc
    refine hxEa ?_
    rw [← hc] at hxy
    exact sameCycle_apply_right.mp hxy
  · intro z hz
    rw [List.tail_cons, List.mem_singleton] at hz
    subst hz
    rcases hplain.cedge_iff.mp hxy with h | h <;> rw [h] <;> simp

open scoped Classical in
omit [Finite D] in
/-- The darts of a contract that lie off the contracted E-link, as a contract of
the double transform. -/
private theorem exists_contract_walkup2 (hplain : G.Plain) (huex : uex.val = G.edge x)
    (l : List D) :
    ∃ l2 : List (Walkup (G.walkupF x) uex), l2.length ≤ l.length ∧
      ∀ w : Walkup (G.walkupF x) uex,
        (w ∈ ((G.walkupF x).walkupF uex).insertE l2 ↔ w.val.val ∈ G.insertE l) := by
  classical
  induction l with
  | nil => exact ⟨[], le_rfl, fun w => by simp⟩
  | cons y t ih =>
    obtain ⟨t2, hlen, hmem⟩ := ih
    by_cases hy : y = x ∨ y = G.edge x
    · refine ⟨t2, by simp only [List.length_cons]; omega, fun w => ?_⟩
      rw [hmem w, insertE_cons, List.mem_cons, List.mem_cons]
      constructor
      · exact fun h => Or.inr (Or.inr h)
      · rintro (h | h | h)
        · rcases hy with h1 | h1
          · exact absurd (h.trans h1) (val_val_ne huex w).1
          · exact absurd (h.trans h1) (val_val_ne huex w).2
        · rcases hy with h1 | h1
          · refine absurd ?_ (val_val_ne huex w).2
            rw [h, h1]
          · refine absurd ?_ (val_val_ne huex w).1
            rw [h, h1, hplain.edge_edge]
        · exact h
    · push Not at hy
      obtain ⟨v, hv⟩ := exists_val_val huex hy.1 hy.2
      refine ⟨v :: t2, by simp only [List.length_cons]; omega, fun w => ?_⟩
      rw [insertE_cons, insertE_cons, List.mem_cons, List.mem_cons, List.mem_cons,
        List.mem_cons, hmem w]
      refine or_congr ?_ (or_congr ?_ Iff.rfl)
      · constructor
        · intro h; rw [h, hv]
        · intro h; exact eq_of_val_val (by rw [hv]; exact h)
      · constructor
        · intro h; rw [h, edge_walkup2 hplain huex v, hv]
        · intro h
          refine eq_of_val_val ?_
          rw [edge_walkup2 hplain huex v, hv]
          exact h

end Contraction

/-! ### Contract colourings -/

section ContractColoring

universe u

open scoped Classical in
/-- **Contracting the E-link at the head of a contract**: a map whose contract
admits no contract ring gives a map with two darts fewer and a no longer
contract, again without contract rings, whose contract colourings lift back. -/
private theorem exists_smaller_contract {E : Type u} [Finite E] (H : Hypermap E)
    (hgeo : H.PlanarBridgelessPlainPrecubic) (x : E) (cc : List E)
    (hno : ∀ q, ¬ H.ContractRing (x :: cc) q) :
    ∃ (E' : Type u) (_ : Finite E') (H' : Hypermap E') (cc' : List E'),
      H'.PlanarBridgelessPlainPrecubic ∧ cc'.length ≤ cc.length ∧
      Nat.card E' + 2 = Nat.card E ∧ (∀ q, ¬ H'.ContractRing cc' q) ∧
      (H'.CcColorable cc' → H.CcColorable (x :: cc)) := by
  classical
  have hplan := hgeo.base.base.planar
  have hbridge := hgeo.base.base.bridgeless
  have hplain := hgeo.base.plain
  have hprecubic := hgeo.precubic
  have hex : H.edge x ≠ x := hplain.edge_ne x
  have huex : (⟨H.edge x, hex⟩ : Walkup H x).val = H.edge x := rfl
  obtain ⟨cc2, hlen2, hEcc⟩ :=
    exists_contract_walkup2 (uex := (⟨H.edge x, hex⟩ : Walkup H x)) hplain huex cc
  have hEcc' : ∀ w : Walkup (H.walkupF x) (⟨H.edge x, hex⟩ : Walkup H x),
      w ∈ ((H.walkupF x).walkupF (⟨H.edge x, hex⟩ : Walkup H x)).insertE cc2
        ↔ w.val.val ∈ H.insertE (x :: cc) := by
    intro w
    rw [hEcc w, insertE_cons, List.mem_cons, List.mem_cons]
    constructor
    · exact fun h => Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact absurd h (val_val_ne huex w).1
      · exact absurd h (val_val_ne huex w).2
      · exact h
  have hplan2 : ((H.walkupF x).walkupF (⟨H.edge x, hex⟩ : Walkup H x)).Planar := by
    have hfin1 : Fintype E := Fintype.ofFinite E
    have hfin2 : Fintype (Walkup H x) := Fintype.ofFinite _
    exact planar_walkupF _ _ (planar_walkupF _ _ hplan)
  refine ⟨Walkup (H.walkupF x) (⟨H.edge x, hex⟩ : Walkup H x), inferInstance,
    (H.walkupF x).walkupF (⟨H.edge x, hex⟩ : Walkup H x), cc2,
    ⟨⟨⟨hplan2, bridgeless_walkup2 hplain hbridge huex hno⟩,
      plain_walkup2 hplain huex⟩, precubic_walkup2 hprecubic⟩, hlen2, ?_, ?_, ?_⟩
  · have h1 : Nat.card E = Nat.card (Walkup H x) + 1 := card_walkup H x
    have h2 : Nat.card (Walkup H x)
        = Nat.card (Walkup (H.walkupF x) (⟨H.edge x, hex⟩ : Walkup H x)) + 1 :=
      card_walkup (H.walkupF x) _
    omega
  · exact no_contractRing_walkup2 hplain hbridge huex hEcc' hno
  · exact fun hcol => ccColorable_of_walkup2 hplain hbridge hprecubic huex hEcc' hcol

/-- The induction behind `Hypermap.contract_coloring`: contracting the E-links
of the contract one at a time until it is empty, at which point minimality
provides a colouring. -/
private theorem ccColorable_aux {nG : ℕ}
    (hmin : ∀ {E : Type u} [Finite E] (H : Hypermap E),
      H.PlanarBridgelessPlainPrecubic → Nat.card E < nG → H.FourColorable) :
    ∀ (n : ℕ) {E : Type u} [Finite E] (H : Hypermap E) (cc : List E),
      H.PlanarBridgelessPlainPrecubic → cc.length ≤ n →
      Nat.card E < (if cc.length = 0 then 0 else 1) + nG →
      (∀ q, ¬ H.ContractRing cc q) → H.CcColorable cc := by
  intro n
  induction n with
  | zero =>
    intro E _ H cc hgeo hlen hcard _
    have hcc : cc = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hcc
    simp only [List.length_nil, reduceIte, Nat.zero_add] at hcard
    obtain ⟨k, hk⟩ := hmin H hgeo hcard
    exact ⟨k, ccColoring_nil_iff.mpr hk⟩
  | succ n ih =>
    intro E _ H cc hgeo hlen hcard hno
    rcases cc with _ | ⟨x, cc'⟩
    · exact ih H [] hgeo (by simp) hcard hno
    · obtain ⟨E', hfin, H', cc2, hgeo', hlen2, hcard2, hno2, hlift⟩ :=
        exists_smaller_contract H hgeo x cc' hno
      have hfinE : Finite E' := hfin
      have hcard1 : Nat.card E < 1 + nG := by
        have hif1 : (if (x :: cc').length = 0 then (0 : ℕ) else 1) = 1 := by simp
        rw [hif1] at hcard
        exact hcard
      refine hlift (ih H' cc2 hgeo' (by simp only [List.length_cons] at hlen; omega) ?_ hno2)
      split <;> omega

omit [DecidableEq D] in
/-- **Every valid contract has a contract colouring.**  This is the reference's
`contract_coloring`, the result the embedding development consumes: contracting
the E-links of `cc` one at a time gives a strictly smaller map, which is
four-colourable by minimality, and the colouring lifts back to a contract
colouring. -/
theorem MinimalCounterExample.contract_coloring (hmin : G.MinimalCounterExample)
    (hB : G.BirkhoffRings) {r cc : List D} (hvc : G.ValidContract r cc) :
    G.CcColorable cc := by
  have hno : ∀ q, ¬ G.ContractRing cc q := by
    rcases Nat.lt_or_ge cc.length 4 with hlt | hge
    · exact contract3_valid hmin hB hvc.sparse (by omega)
    · have h4 : cc.length = 4 := le_antisymm hvc.size_le hge
      obtain ⟨x0, -, ht⟩ := hvc.triad h4
      exact triad_valid hmin hB hvc.sparse h4 ht
  have hne : cc.length ≠ 0 := by have := hvc.one_le_size; omega
  have hif : (if cc.length = 0 then (0 : ℕ) else 1) = 1 := by simp [hne]
  refine ccColorable_aux (nG := Nat.card D) ?_ cc.length G cc hmin.base le_rfl ?_ hno
  · intro E _ H hgeo hlt
    exact hmin.minimal H hgeo hlt
  · rw [hif]
    omega

end ContractColoring


end DoubleWalkup

end Walkup

end Finite

end Hypermap

end FourColor


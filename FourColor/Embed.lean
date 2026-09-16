import FourColor.Contract

/-!
# The embedding theorem

This file is the crux of the Four Colour Theorem: from the partial embedding
produced by the part quiz one builds a genuine injective embedding of a
configuration map into a minimal counter-example, and then derives a
contradiction from C-reducibility.

Everything happens in one context: an embeddable ring `rc` in a configuration
map `Gc`, and a preembedding `h` of the kernel of `rc` into a hypermap `Gm`.
The results below take these as explicit hypotheses rather than as section
variables of a single contradiction section, so that each of them can be used
on its own.

## Main definitions

* `Hypermap.embed` — the extension of the preembedding `h` from the kernel of
  `rc` to every dart off `rc`, by the four cases of `Hypermap.embed_cases`.
* `Hypermap.PreHomRing` — an R-link path in the kernel whose image under the
  preembedding is a face-simple R-cycle.
* `Hypermap.embedDisk`, `Hypermap.embd`, `Hypermap.embdRing`, `Hypermap.embdd` —
  the disk map carried by the darts off the perimeter, its projection into `Gc`,
  its border and its projection into `Gm`.
* `Hypermap.embedRem`, `Hypermap.embr`, `Hypermap.embrRing` — the remainder map
  carried by the darts of `Gm` that the interior of the disk map misses, its
  projection and its border.
* `Hypermap.embedCotrace` — the ring traces on the border of the remainder map.

## Main results

* `Hypermap.cface_h`, `Hypermap.exists_cface_h` — the preembedding maps a face
  of the kernel onto a face, surjectively.
* `Hypermap.cface_inj_embed` — the preembedding is injective on each face of
  the kernel.
* `Hypermap.edge_perimeter` — no E-link has both its darts on the perimeter.
* `Hypermap.chordless_perimeter` — of the two darts of an E-link off the
  perimeter, at least one lies in the kernel.
* `Hypermap.fcard_adj_perimeter` — a face outside the kernel has exactly two
  darts whose E-link meets the perimeter.
* `Hypermap.adj_kernel_min`, `Hypermap.adj_kernel_max` — consequently such a
  face has between one and four darts pointing into the kernel.
* `Hypermap.embed_cases` — every dart is covered by one of the four cases that
  define `Hypermap.embed`.
* `Hypermap.embed_functor` — the preembedding commutes with `edge` everywhere on
  the kernel, which is what makes it a genuine partial morphism.
* `Hypermap.rlink_map_embed`, `Hypermap.isChain_map_embed`,
  `Hypermap.intro_preHomRing` — the image of an R-link path of the kernel is an
  R-link path, and the introduction rule for `Hypermap.PreHomRing`.
* `Hypermap.trivial_hom_ring` — a homomorphic ring whose image bounds no face
  closes up into an R-cycle.
* `Hypermap.embed_full` — the preembedding reflects E-links.
* `Hypermap.pre_embed_inj` — the preembedding is injective on the kernel.
* `Hypermap.embedE`, `Hypermap.embedN`, `Hypermap.embed_inj` — the extension is
  a morphism for `edge` everywhere and for `node` off the perimeter, and it is
  injective off the perimeter.
* `Hypermap.cface_embd`, `Hypermap.scycle_embd_ring`, `Hypermap.embdd_inj`,
  `Hypermap.embddE`, `Hypermap.embddN` — the disk map and its two projections.
* `Hypermap.embed_patch` — the disk map and the remainder map patch `Gm`.
* `Hypermap.planar_embr`, `Hypermap.plain_embr`, `Hypermap.cubic_embr` — the
  remainder map is a planar, plain, quasicubic configuration map.
* `Hypermap.embed_sparse` — the image of a valid contract is node-simple.
* `Hypermap.embed_closure` — the cotrace of the remainder map is Kempe-closed.
* `Hypermap.cface_embed_iff` — the extension reflects as well as preserves the
  face relation off the perimeter.
* `Hypermap.embed_valid_contract` — the image of a valid contract of `rc` is a
  valid contract of the remainder map, with an empty ring.
* `Hypermap.embed_contract` — a colouring of the contracted target restricts to
  a ring trace of `rc` that is also a cotrace of the remainder map.
* `Hypermap.not_embed_reducible` — **a C-reducible configuration cannot be
  embedded in a minimal counter-example.**

## Status

This completes the port of `theories/proof/embed.v`: every step of the
reference, up to and including `not_embed_reducible`, is proved here.  Every
declaration below is fully proved, with no `sorry` and no new axioms.

## References

Georges Gonthier, *Formal Proof — The Four-Color Theorem*; this file
corresponds to `theories/proof/embed.v` of the Coq development.
-/


namespace FourColor

namespace Hypermap

open Equiv Equiv.Perm

section Embeddings

variable {Dc Dm : Type*} [Finite Dc] [Finite Dm] {Gc : Hypermap Dc} {Gm : Hypermap Dm}
variable {rc : List Dc} {h : Dc → Dm}

/-! ### The perimeter of a configuration map

The perimeter `rc` is a node orbit, so it is closed under `node`; and because
the faces it meets have at least three darts, it never contains both darts of
an E-link. -/

/-- The perimeter is a node orbit, hence closed under `node`. -/
theorem node_mem_ring_iff (hemb : Gc.Embeddable rc) (x : Dc) :
    Gc.node x ∈ rc ↔ x ∈ rc :=
  node_mem_iff_mem hemb.base.base.base.cycle x

/-- **No E-link has both its darts on the perimeter.**  This is the reference's
`edge_perimeter`. -/
theorem edge_perimeter (hemb : Gc.Embeddable rc) (x : Dc) :
    x ∉ rc ∨ Gc.edge x ∉ rc := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hx, hex⟩ := hcon
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hfx : Gc.face x ∈ rc := by
    rw [← node_mem_ring_iff hemb, hplain.node_face]
    exact hex
  have hfix : Gc.face x = x :=
    (hemb.base.simple.eq_of_cface hfx hx (Gc.cface_face x).symm)
  have h1 : Gc.arity x ≤ 1 := by
    refine Function.IsPeriodicPt.minimalPeriod_le Nat.one_pos ?_
    change Gc.face^[1] x = x
    simpa using hfix
  exact absurd ((hemb.ringArity x hx).1.trans h1) (by omega)

omit [Finite Dc] in
/-- The reverse perimeter is a face-simple R-cycle. -/
theorem scycle_reverse_ring (hemb : Gc.Embeddable rc) :
    Gc.Scycle Gc.Rlink rc.reverse := by
  refine ⟨?_, by simpa using hemb.base.simple⟩
  refine IsCyclicChain.congr ?_ hemb.base.base.base.cycle.reverse
  rintro u v rfl
  exact cface_edge_node Gc v

omit [Finite Dc] in
/-- The reverse ring of the reverse perimeter is the E-image of the
perimeter. -/
theorem revRing_reverse_ring (Gc : Hypermap Dc) (rc : List Dc) :
    Gc.revRing rc.reverse = rc.map Gc.edge := by
  simp [revRing]

omit [Finite Dc] in
/-- The E-image of the perimeter is a face-simple R-cycle. -/
theorem scycle_edge_ring (hemb : Gc.Embeddable rc) :
    Gc.Scycle Gc.Rlink (rc.map Gc.edge) := by
  rw [← revRing_reverse_ring]
  exact scycle_revRing hemb.base.base.base.base.plain (scycle_reverse_ring hemb)

omit [Finite Dc] in
/-- The E-image of the perimeter meets exactly the faces that the perimeter
meets. -/
theorem fband_edge_ring_iff (hemb : Gc.Embeddable rc) (y : Dc) :
    Gc.Fband (rc.map Gc.edge) y ↔ Gc.Fband rc y := by
  rw [← revRing_reverse_ring,
    fband_revRing hemb.base.base.base.base.plain (scycle_reverse_ring hemb)]
  simp

/-! ### Basic properties of the preembedding

The preembedding commutes with `face` on the kernel, so it maps faces of the
kernel into faces of the target, injectively because it preserves arity. -/

section Preembed

omit [Finite Dc] in
/-- A dart lies in the face of each of its `face`-iterates. -/
theorem cface_iterate (G : Hypermap Dc) (n : ℕ) (x : Dc) : G.CFace x (G.face^[n] x) :=
  ⟨(n : ℤ), by rw [zpow_natCast, Perm.coe_pow]⟩

omit [Finite Dc] [Finite Dm] in
/-- On the kernel the preembedding commutes with every iterate of `face`. -/
theorem h_iterate_face (hpre : Preembedding Gc Gm h {x | Gc.Kernel rc x})
    {x : Dc} (hx : Gc.Kernel rc x) (n : ℕ) :
    h (Gc.face^[n] x) = Gm.face^[n] (h x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (show Gc.Kernel rc (Gc.face x) from kernel_face.mpr hx), hpre.face x hx]

omit [Finite Dm] in
/-- The preembedding maps a face of the kernel into a face.  This is the
reference's `cface_ac_h`. -/
theorem cface_h (hpre : Preembedding Gc Gm h {x | Gc.Kernel rc x})
    {x y : Dc} (hx : Gc.Kernel rc x) (hxy : Gc.CFace x y) : Gm.CFace (h x) (h y) := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  rw [← hn, h_iterate_face hpre hx]
  exact cface_iterate Gm n (h x)

omit [Finite Dc] in
/-- Every dart in the face of the image of a kernel dart is itself the image of
a dart of that face.  This is the reference's `cface_h_ac`. -/
theorem exists_cface_h (hpre : Preembedding Gc Gm h {x | Gc.Kernel rc x})
    {x : Dc} {u : Dm} (hx : Gc.Kernel rc x) (hxu : Gm.CFace (h x) u) :
    ∃ y, Gc.CFace x y ∧ h y = u := by
  obtain ⟨n, hn⟩ := hxu.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  exact ⟨Gc.face^[n] x, cface_iterate Gc n x, by rw [h_iterate_face hpre hx, hn]⟩

omit [Finite Dm] in
/-- **The preembedding is injective on each face of the kernel.**  This is the
reference's `cface_inj_embed`. -/
theorem cface_inj_embed (hpre : Preembedding Gc Gm h {x | Gc.Kernel rc x})
    {x y : Dc} (hx : Gc.Kernel rc x) (hxy : Gc.CFace x y) (heq : h x = h y) : x = y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  have hper : Function.IsPeriodicPt Gc.face (Gc.arity x) x := Function.iterate_minimalPeriod
  set m := n % Gc.arity x with hm
  have hmy : Gc.face^[m] x = y := by rw [hm, hper.iterate_mod_apply, hn]
  have hlt : m < Gc.arity x := Nat.mod_lt _ (Gc.arity_pos x)
  have hfix : Gm.face^[m] (h x) = h x := by
    rw [← h_iterate_face hpre hx, hmy, ← heq]
  have hdvd : Gm.arity (h x) ∣ m :=
    Function.IsPeriodicPt.minimalPeriod_dvd (x := h x) (n := m) hfix
  rw [hpre.arity x hx] at hdvd
  have hm0 : m = 0 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact h0
    · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  rw [← hmy, hm0]
  rfl

end Preembed

/-! ### Chordlessness of the perimeter

The E-image `rc.map edge` of the perimeter is an R-cycle whose disk is the
kernel side of the configuration.  A chord of that cycle would cut off a disk
containing no face at all, which the arity bound on the perimeter faces
forbids. -/

section Chordless

omit [Finite Dc] in
/-- A dart whose face closes up after two steps has arity at most two. -/
private theorem arity_le_two {z : Dc} (h : Gc.face (Gc.face z) = z) : Gc.arity z ≤ 2 := by
  refine Function.IsPeriodicPt.minimalPeriod_le (n := 2) (by norm_num) ?_
  change (Gc.face : Dc → Dc)^[2] z = z
  simpa [Function.iterate_succ_apply'] using h

/-- **Every ring made of perimeter E-links bounds a face.**  This is the inner
induction of the reference's `chordless_perimeter`: a face-simple proper
R-cycle whose darts, apart from its head, are E-images of perimeter darts and
whose disk avoids the perimeter, has a face strictly inside it. -/
private theorem exists_diskF_ring (hemb : Gc.Embeddable rc) (n : ℕ) :
    ∀ p : List Dc, p.length ≤ n → Gc.Scycle Gc.Rlink p → Gc.ProperRing p →
      (∀ z ∈ p.tail, z ∈ rc.map Gc.edge) → (∀ z, Gc.DiskN p z → z ∉ rc) →
      ∃ y, Gc.DiskF p y := by
  classical
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hplan : Gc.Planar := hemb.base.planar
  have hbridge : Gc.Bridgeless := hemb.base.bridgeless
  have hconn : Gc.Connected := hemb.base.base.connected
  have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
  induction n with
  | zero =>
    intro p hlen _ hproper _ _
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    exact absurd hproper (by simp)
  | succ n ih =>
  intro p hlen hscyc hproper htail hdN
  by_contra hcontra
  simp only [not_exists] at hcontra
  have hnodup : p.Nodup := hscyc.nodup
  have hsimple : Gc.Simple p := hscyc.simple
  have hcyc : IsCyclicChain Gc.Rlink p := hscyc.isCyclicChain
  obtain ⟨x, z1, p1, hp⟩ : ∃ x z1 p1, p = x :: z1 :: p1 := by
    match p, hproper with
    | [], hpr => exact (Gc.properRing_nil hpr).elim
    | [a], hpr => exact (Gc.properRing_singleton a hpr).elim
    | x :: z1 :: p1, _ => exact ⟨x, z1, p1, rfl⟩
  have hcyc' : IsCyclicChain Gc.Rlink (x :: z1 :: p1) := by rw [← hp]; exact hcyc
  have hpx : x ∈ p := by rw [hp]; exact List.mem_cons_self
  have hz1mem : z1 ∈ p := by rw [hp]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hrl1 : Gc.Rlink x z1 := (List.isChain_cons_cons.mp hcyc'.isChain).1
  have hdNx : Gc.DiskN p x := diskN_of_mem hpx
  have hbcx : x ∉ rc := hdN x hdNx
  have hn3x : Gc.node (Gc.node (Gc.node x)) = x := hqc.node_node_node hbcx
  have hnxne : Gc.node x ≠ x := hqc.node_ne hbcx
  have hfe : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
    have hk := Gc.nodeK (Gc.node (Gc.node x))
    rwa [hn3x] at hk
  have hfefex : Gc.face (Gc.edge (Gc.face (Gc.edge x))) = Gc.node x := by
    rw [hfe]; exact Gc.nodeK (Gc.node x)
  have heefex : Gc.edge (Gc.edge (Gc.face (Gc.edge x))) = Gc.face (Gc.edge x) :=
    hplain.edge_edge _
  by_cases hdE : Gc.DiskE p (Gc.edge (Gc.face (Gc.edge x)))
  · -- the chord runs strictly inside the ring: cut along it
    have hbandefex : Gc.Fband p (Gc.edge (Gc.face (Gc.edge x))) := by
      by_contra hnb
      refine hcontra (Gc.node x) ⟨diskN_node hdNx, ?_⟩
      rw [← hfefex, fband_face]
      exact hnb
    have hbandfex : Gc.Fband p (Gc.face (Gc.edge x)) :=
      ⟨p.next x hpx, List.next_mem _ _ _,
        (Gc.cface_face (Gc.edge x)).symm.trans (rel_next hcyc hnodup hpx)⟩
    have hbandeefex : Gc.Fband p (Gc.edge (Gc.edge (Gc.face (Gc.edge x)))) := by
      rw [heefex]; exact hbandfex
    have hzeq : Gc.fproj p (Gc.edge (Gc.edge (Gc.face (Gc.edge x)))) = z1 := by
      have heq : Gc.fproj p (Gc.face (Gc.edge x)) = z1 := by
        refine hsimple.eq_of_cface (fproj_mem hbandfex) hz1mem ?_
        exact (((Gc.cface_face (Gc.edge x)).trans (Gc.cface_fproj _)).symm).trans hrl1
      rw [heefex]; exact heq
    have hcez1 : Gc.CFace (Gc.edge (Gc.edge (Gc.face (Gc.edge x)))) z1 := by
      rw [← hzeq]; exact Gc.cface_fproj _
    obtain ⟨y, hydef⟩ : ∃ y, y = Gc.fproj p (Gc.edge (Gc.face (Gc.edge x))) := ⟨_, rfl⟩
    have hymem : y ∈ p := by rw [hydef]; exact fproj_mem hbandefex
    have hcy : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) y := by
      rw [hydef]; exact Gc.cface_fproj _
    have hynex : y ≠ x := by
      intro hyx
      refine hbridge.not_cface_node x ?_
      have hcf : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) (Gc.node x) := by
        rw [← hfefex]; exact Gc.cface_face _
      exact hcf.symm.trans (hyx ▸ hcy)
    have hynez1 : y ≠ z1 := by
      intro hyz
      exact hbridge _ ((hyz ▸ hcy).trans hcez1.symm)
    have hyp1 : y ∈ p1 := by
      have hym := hymem
      rw [hp] at hym
      rcases List.mem_cons.mp hym with hc | hc
      · exact absurd hc hynex
      · exact (List.mem_cons.mp hc).resolve_left hynez1
    obtain ⟨p2, p3, hp1⟩ := List.append_of_mem hyp1
    have hchord : Gc.chordRing p (Gc.edge (Gc.face (Gc.edge x)))
        = Gc.edge (Gc.face (Gc.edge x)) :: z1 :: p2 := by
      have hrot : p.rotate 1 = z1 :: (p2 ++ (y :: (p3 ++ [x]))) := by
        rw [hp, hp1]; simp
      have hrotTo : rotTo p z1 = (z1 :: p2) ++ (y :: (p3 ++ [x])) :=
        rotTo_eq_of_rotate hnodup (m := 1) hrot
      have hynotin : y ∉ z1 :: p2 := by
        have hnd : (x :: z1 :: (p2 ++ y :: p3)).Nodup := by rw [← hp1, ← hp]; exact hnodup
        have hnd2 : (p2 ++ y :: p3).Nodup :=
          (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
        obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd2
        intro hc
        rcases List.mem_cons.mp hc with hc | hc
        · exact hynez1 hc
        · exact hdisj y hc y List.mem_cons_self rfl
      have harc : arc p z1 y = z1 :: p2 := arc_eq_of_rotTo hrotTo hynotin
      simp only [chordRing, hzeq, ← hydef, harc]
    have hlen2 : (Gc.chordRing p (Gc.edge (Gc.face (Gc.edge x)))).length ≤ n := by
      rw [hchord]
      rw [hp, hp1] at hlen
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega
    have hscyc2 := scycle_chordRing hplain hbridge hscyc hbandefex hbandeefex
    have hproper2 :=
      properRing_chordRing hplan hplain hbridge hscyc hdE hbandefex hbandeefex
    have htail2 : ∀ w ∈ (Gc.chordRing p (Gc.edge (Gc.face (Gc.edge x)))).tail,
        w ∈ rc.map Gc.edge := by
      rw [hchord]
      intro w hw
      refine htail w ?_
      rw [hp]
      simp only [List.tail_cons]
      rcases List.mem_cons.mp hw with hc | hc
      · exact hc ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (by rw [hp1, List.mem_append]; exact Or.inl hc)
    have hdN2 : ∀ w, Gc.DiskN (Gc.chordRing p (Gc.edge (Gc.face (Gc.edge x)))) w → w ∉ rc :=
      fun w hw => hdN w ((diskN_chordRing hplan hplain hbridge hconn hscyc hproper hdE
        hbandefex hbandeefex).mp hw).1
    obtain ⟨w, hw⟩ := ih _ hlen2 hscyc2 hproper2 htail2 hdN2
    exact hcontra w ((diskF_chordRing hplan hplain hbridge hconn hscyc hproper hdE
      hbandefex hbandeefex).mp hw).1
  · -- the chord lies on the ring: the ring runs through `face (edge x)`
    have hdNfex : Gc.DiskN p (Gc.face (Gc.edge x)) := by
      rw [hfe]; exact diskN_node (diskN_node hdNx)
    have hfexp : Gc.face (Gc.edge x) ∈ p := by
      by_contra hnm
      exact hdE ((diskE_edge_iff hplan hscyc).mpr ⟨hdNfex, hnm⟩)
    have hz1fex : z1 = Gc.face (Gc.edge x) :=
      hsimple.eq_of_cface hz1mem hfexp (hrl1.symm.trans (Gc.cface_face (Gc.edge x)))
    have hcfenxx : Gc.CFace (Gc.edge (Gc.node x)) x := by
      have h0 := Gc.cface_face (Gc.edge (Gc.node x))
      rw [Gc.nodeK x] at h0
      exact h0
    have hbandenx : Gc.Fband p (Gc.edge (Gc.node x)) := ⟨x, hpx, hcfenxx⟩
    obtain ⟨zz, p3, hp1⟩ : ∃ zz p3, p1 = zz :: p3 := by
      match p1, hcyc' with
      | [], hcc =>
        exfalso
        have hlast : Gc.Rlink z1 x := by
          have hl := (isCyclicChain_cons.mp hcc).2
          simpa using hl
        refine hbridge.not_cface_node x ?_
        have h1 : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) x := by
          rw [← hz1fex]; exact hlast
        have hcf : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) (Gc.node x) := by
          rw [← hfefex]; exact Gc.cface_face _
        exact hcf.symm.trans h1
      | zz :: p3, _ => exact ⟨zz, p3, rfl⟩
    have hzzmem : zz ∈ p := by
      rw [hp, hp1]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hrl2 : Gc.Rlink z1 zz := by
      have hch := (List.isChain_cons_cons.mp hcyc'.isChain).2
      rw [hp1] at hch
      exact (List.isChain_cons_cons.mp hch).1
    have hcfnxzz : Gc.CFace (Gc.node x) zz := by
      have h1 : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) zz := by
        rw [← hz1fex]; exact hrl2
      have hcf : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) (Gc.node x) := by
        rw [← hfefex]; exact Gc.cface_face _
      exact hcf.symm.trans h1
    have hbandnx : Gc.Fband p (Gc.node x) := ⟨zz, hzzmem, hcfnxzz⟩
    have hbandeenx : Gc.Fband p (Gc.edge (Gc.edge (Gc.node x))) := by
      rw [hplain.edge_edge]; exact hbandnx
    have hnxnotp : Gc.node x ∉ p := by
      rw [hp]
      simp only [List.mem_cons, not_or]
      refine ⟨hnxne, ?_, ?_⟩
      · rw [hz1fex, hfe]
        exact fun hc => hnxne (Gc.node.injective hc).symm
      · intro hin
        have hercnx : Gc.node x ∈ rc.map Gc.edge := by
          refine htail _ ?_
          rw [hp]; exact List.mem_cons_of_mem _ hin
        obtain ⟨w, hwrc, hw⟩ := List.mem_map.mp hercnx
        have hrcenx : Gc.edge (Gc.node x) ∈ rc := by
          rw [← hw, hplain.edge_edge]; exact hwrc
        have hercz1 : z1 ∈ rc.map Gc.edge := by
          refine htail _ ?_
          rw [hp]; exact List.mem_cons_self
        obtain ⟨w', hw'rc, hw'⟩ := List.mem_map.mp hercz1
        have hrcefex : Gc.edge (Gc.face (Gc.edge x)) ∈ rc := by
          rw [← hz1fex, ← hw', hplain.edge_edge]; exact hw'rc
        have hrcfnx : Gc.face (Gc.node x) ∈ rc := by
          rw [← node_mem_ring_iff hemb, hplain.node_face]
          exact hrcenx
        have hcf : Gc.CFace (Gc.edge (Gc.face (Gc.edge x))) (Gc.node x) := by
          rw [← hfefex]; exact Gc.cface_face _
        have hcfnx : Gc.CFace (Gc.face (Gc.node x)) (Gc.edge (Gc.face (Gc.edge x))) :=
          ((Gc.cface_face (Gc.node x)).symm).trans hcf.symm
        have hfnx : Gc.face (Gc.node x) = Gc.edge (Gc.face (Gc.edge x)) :=
          hemb.base.simple.eq_of_cface hrcfnx hrcefex hcfnx
        have h2 : Gc.arity (Gc.edge (Gc.face (Gc.edge x))) ≤ 2 :=
          arity_le_two (by rw [hfefex, hfnx])
        exact absurd ((hemb.ringArity _ hrcefex).1.trans h2) (by omega)
    have hdEenx : Gc.DiskE p (Gc.edge (Gc.node x)) := by
      rw [diskE_edge_iff hplan hscyc]
      exact ⟨diskN_node hdNx, hnxnotp⟩
    have hfprojenx : Gc.fproj p (Gc.edge (Gc.node x)) = x := by
      exact hsimple.eq_of_cface (fproj_mem hbandenx) hpx
        ((Gc.cface_fproj _).symm.trans hcfenxx)
    have hfprojeenx : Gc.fproj p (Gc.edge (Gc.edge (Gc.node x))) = zz := by
      rw [hplain.edge_edge]
      exact hsimple.eq_of_cface (fproj_mem hbandnx) hzzmem
        ((Gc.cface_fproj _).symm.trans hcfnxzz)
    have hchord : Gc.chordRing p (Gc.edge (Gc.node x))
        = Gc.edge (Gc.node x) :: zz :: p3 := by
      have hrot : p.rotate 2 = zz :: (p3 ++ (x :: [z1])) := by
        rw [hp, hp1]; simp
      have hrotTo : rotTo p zz = (zz :: p3) ++ (x :: [z1]) :=
        rotTo_eq_of_rotate hnodup (m := 2) hrot
      have hxnotin : x ∉ zz :: p3 := by
        have hnd : (x :: z1 :: zz :: p3).Nodup := by rw [← hp1, ← hp]; exact hnodup
        intro hc
        exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hc)
      have harc : arc p zz x = zz :: p3 := arc_eq_of_rotTo hrotTo hxnotin
      simp only [chordRing, hfprojeenx, hfprojenx, harc]
    have hlen2 : (Gc.chordRing p (Gc.edge (Gc.node x))).length ≤ n := by
      rw [hchord]
      rw [hp, hp1] at hlen
      simp only [List.length_cons] at hlen ⊢
      omega
    have hscyc2 := scycle_chordRing hplain hbridge hscyc hbandenx hbandeenx
    have hproper2 :=
      properRing_chordRing hplan hplain hbridge hscyc hdEenx hbandenx hbandeenx
    have htail2 : ∀ w ∈ (Gc.chordRing p (Gc.edge (Gc.node x))).tail, w ∈ rc.map Gc.edge := by
      rw [hchord]
      intro w hw
      refine htail w ?_
      rw [hp]
      simp only [List.tail_cons]
      exact List.mem_cons_of_mem _ (by rw [hp1]; exact hw)
    have hdN2 : ∀ w, Gc.DiskN (Gc.chordRing p (Gc.edge (Gc.node x))) w → w ∉ rc :=
      fun w hw => hdN w ((diskN_chordRing hplan hplain hbridge hconn hscyc hproper hdEenx
        hbandenx hbandeenx).mp hw).1
    obtain ⟨w, hw⟩ := ih _ hlen2 hscyc2 hproper2 htail2 hdN2
    exact hcontra w ((diskF_chordRing hplan hplain hbridge hconn hscyc hproper hdEenx
      hbandenx hbandeenx).mp hw).1

/-- The E-image of the perimeter is a proper ring. -/
private theorem properRing_edge_ring (hemb : Gc.Embeddable rc) (hne : rc ≠ []) :
    Gc.ProperRing (rc.map Gc.edge) := by
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hbridge : Gc.Bridgeless := hemb.base.bridgeless
  have hscyc := scycle_edge_ring hemb
  have hperim := edge_perimeter hemb
  clear hemb
  rcases rc with _ | ⟨a, t⟩
  · exact absurd rfl hne
  · rcases t with _ | ⟨b, t⟩
    · exfalso
      have hl : Gc.Rlink (Gc.edge a) (Gc.edge a) := by
        have hc := hscyc.isCyclicChain
        simpa using hc
      have hl2 : Gc.CFace (Gc.edge (Gc.edge a)) (Gc.edge a) := hl
      rw [hplain.edge_edge] at hl2
      exact hbridge a hl2
    · rcases t with _ | ⟨c, t⟩
      · simp only [List.map_cons, List.map_nil, properRing_pair]
        intro hcon
        rw [hplain.edge_edge] at hcon
        have hab : Gc.edge a = b := by rw [hcon, hplain.edge_edge]
        rcases hperim a with hp | hp
        · exact hp List.mem_cons_self
        · exact hp (by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      · have hlen : 2 < ((a :: b :: c :: t).map Gc.edge).length := by
          simp only [List.length_map, List.length_cons]
          omega
        exact Gc.properRing_of_two_lt_length hlen

/-- The reverse perimeter is a proper ring. -/
private theorem properRing_reverse_ring (hemb : Gc.Embeddable rc) (hne : rc ≠ []) :
    Gc.ProperRing rc.reverse := by
  rw [← properRing_revRing hemb.base.base.base.base.plain, revRing_reverse_ring]
  exact properRing_edge_ring hemb hne

/-- **A chord of the E-image of the perimeter bounds a face.**  This is the
reference's `nt_dFerc`. -/
private theorem exists_diskF_chordRing (hemb : Gc.Embeddable rc) {c : Dc}
    (hcb : Gc.Fband (rc.map Gc.edge) c) (hceb : Gc.Fband (rc.map Gc.edge) (Gc.edge c))
    (hdE : Gc.DiskE (rc.map Gc.edge) c) :
    ∃ y, Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) y := by
  classical
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hplan : Gc.Planar := hemb.base.planar
  have hbridge : Gc.Bridgeless := hemb.base.bridgeless
  have hconn : Gc.Connected := hemb.base.base.connected
  have hrcne : rc ≠ [] := by rintro rfl; simp at hcb
  have hperc := properRing_edge_ring hemb hrcne
  have hUerc := scycle_edge_ring hemb
  refine exists_diskF_ring hemb (Gc.chordRing (rc.map Gc.edge) c).length _ le_rfl
    (scycle_chordRing hplain hbridge hUerc hcb hceb)
    (properRing_chordRing hplan hplain hbridge hUerc hdE hcb hceb) ?_ ?_
  · intro w hw
    have hteq : (Gc.chordRing (rc.map Gc.edge) c).tail
        = arc (rc.map Gc.edge) (Gc.fproj (rc.map Gc.edge) (Gc.edge c))
            (Gc.fproj (rc.map Gc.edge) c) := by
      simp only [chordRing, List.tail_cons]
    rw [hteq] at hw
    exact mem_of_mem_arc hw
  · intro w hw hwrc
    have hN : Gc.DiskN (rc.map Gc.edge) w :=
      ((diskN_chordRing hplan hplain hbridge hconn hUerc hperc hdE hcb hceb).mp hw).1
    rw [← revRing_reverse_ring, diskN_revRing hplan hplain hconn
      (scycle_reverse_ring hemb) (properRing_reverse_ring hemb hrcne)] at hN
    exact hN (diskN_of_mem (by rw [List.mem_reverse]; exact hwrc))

omit [Finite Dm] in
/-- **The disk cut off by a chord of the perimeter is exactly the kernel.**
This is the reference's `dFerc_ac`. -/
private theorem diskF_chordRing_eq_kernel (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {c : Dc}
    (hcb : Gc.Fband (rc.map Gc.edge) c) (hceb : Gc.Fband (rc.map Gc.edge) (Gc.edge c))
    (hdE : Gc.DiskE (rc.map Gc.edge) c) (z : Dc) :
    Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) z ↔ Gc.Kernel rc z := by
  classical
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hplan : Gc.Planar := hemb.base.planar
  have hbridge : Gc.Bridgeless := hemb.base.bridgeless
  have hconn : Gc.Connected := hemb.base.base.connected
  have hrcne : rc ≠ [] := by rintro rfl; simp at hcb
  have hperc := properRing_edge_ring hemb hrcne
  have hUerc := scycle_edge_ring hemb
  have hfwd : ∀ w, Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) w → Gc.Kernel rc w := by
    intro w hwF hb
    exact ((diskF_chordRing hplan hplain hbridge hconn hUerc hperc hdE hcb hceb).mp
      hwF).1.2 ((fband_edge_ring_iff hemb w).mpr hb)
  refine ⟨hfwd z, fun hz => ?_⟩
  -- inside the kernel, being in the disk is enough to be strictly inside it
  have hdNdF : ∀ w, Gc.Kernel rc w → Gc.DiskN (Gc.chordRing (rc.map Gc.edge) c) w →
      Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) w := by
    intro w hw hN
    refine ⟨hN, fun hb => hw ?_⟩
    exact (fband_edge_ring_iff hemb w).mp
      ((fband_chordRing hplain hbridge hUerc hcb hceb).mp (Or.inl hb))
  -- an R-link path inside the kernel stays inside the disk
  have hstep : ∀ (q : List Dc) (w : Dc),
      Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) w → List.IsChain Gc.Rlink (w :: q) →
      (∀ t ∈ q, Gc.Kernel rc t) →
      Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) (q.getLastD w) := by
    intro q
    induction q with
    | nil => intro w hw _ _; exact hw
    | cons a q ih =>
      intro w hw hchain hker
      have hlink : Gc.Rlink w a := (List.isChain_cons_cons.mp hchain).1
      have hchain' : List.IsChain Gc.Rlink (a :: q) := (List.isChain_cons_cons.mp hchain).2
      have hka : Gc.Kernel rc a := hker a List.mem_cons_self
      have hcfa : Gc.CFace (Gc.face (Gc.edge w)) a :=
        (Gc.cface_face (Gc.edge w)).symm.trans hlink
      have hdn : Gc.DiskN (Gc.chordRing (rc.map Gc.edge) c) (Gc.face (Gc.edge w)) := by
        refine diskN_node_iff.mp ?_
        rw [Gc.edgeK w]
        exact hw.1
      have hkfa : Gc.Kernel rc (Gc.face (Gc.edge w)) := (Kernel.congr hcfa).mpr hka
      have hfa : Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) a :=
        (diskF_congr hcfa).mp (hdNdF _ hkfa hdn)
      rw [List.getLastD_cons]
      exact ih a hfa hchain' (fun t ht => hker t (List.mem_cons_of_mem _ ht))
  obtain ⟨y0, hy0⟩ := exists_diskF_chordRing hemb hcb hceb hdE
  have hkey0 : Gc.edge (Gc.edge y0) ∈ {w : Dc | Gc.Kernel rc w} := by
    change Gc.Kernel rc (Gc.edge (Gc.edge y0))
    rw [hplain.edge_edge]
    exact hfwd y0 hy0
  obtain ⟨q, hqne, hqchain, hqlast, -, hqmem⟩ :=
    hpre.simple_path (fun u v huv hu => (Kernel.congr huv).mp hu) hkey0 hz
  rcases q with _ | ⟨y1, q'⟩
  · exact absurd rfl hqne
  · have hlink1 : Gc.Rlink (Gc.edge y0) y1 := (List.isChain_cons_cons.mp hqchain).1
    have hcf1 : Gc.CFace y0 y1 := by
      have hc : Gc.CFace (Gc.edge (Gc.edge y0)) y1 := hlink1
      rwa [hplain.edge_edge] at hc
    have hf1 : Gc.DiskF (Gc.chordRing (rc.map Gc.edge) c) y1 := (diskF_congr hcf1).mp hy0
    have hchain' : List.IsChain Gc.Rlink (y1 :: q') := (List.isChain_cons_cons.mp hqchain).2
    have hlast := hstep q' y1 hf1 hchain' (fun t ht => (hqmem t (List.mem_cons_of_mem _ ht)).1)
    rw [List.getLastD_cons] at hqlast
    exact (diskF_congr hqlast).mp hlast

omit [Finite Dm] in
/-- **Of the two darts of an E-link off the perimeter, one lies in the
kernel.**  This is the reference's `chordless_perimeter`. -/
theorem chordless_perimeter (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc}
    (hx : x ∉ rc) (hex : Gc.edge x ∉ rc) :
    Gc.Kernel rc x ∨ Gc.Kernel rc (Gc.edge x) := by
  classical
  by_contra hcon
  have hb1 : Gc.Fband rc x := by by_contra hb; exact hcon (Or.inl hb)
  have hb2 : Gc.Fband rc (Gc.edge x) := by by_contra hb; exact hcon (Or.inr hb)
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hplan : Gc.Planar := hemb.base.planar
  have hbridge : Gc.Bridgeless := hemb.base.bridgeless
  have hconn : Gc.Connected := hemb.base.base.connected
  have hrcne : rc ≠ [] := by rintro rfl; simp at hb1
  have hperc := properRing_edge_ring hemb hrcne
  have hUerc := scycle_edge_ring hemb
  have hbx : Gc.Fband (rc.map Gc.edge) x := (fband_edge_ring_iff hemb x).mpr hb1
  have hbex : Gc.Fband (rc.map Gc.edge) (Gc.edge x) := (fband_edge_ring_iff hemb _).mpr hb2
  have hbeex : Gc.Fband (rc.map Gc.edge) (Gc.edge (Gc.edge x)) := by
    rw [hplain.edge_edge]; exact hbx
  have hdNex : Gc.DiskN (rc.map Gc.edge) (Gc.edge x) := by
    rw [← revRing_reverse_ring, diskN_revRing hplan hplain hconn
      (scycle_reverse_ring hemb) (properRing_reverse_ring hemb hrcne)]
    rintro ⟨w, hw, hpath⟩
    have hwrc : w ∈ rc := by rwa [List.mem_reverse] at hw
    have hnw : Gc.node⁻¹ w ∈ rc.reverse := by
      rw [List.mem_reverse, ← node_mem_ring_iff hemb]
      simpa using hwrc
    rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨u, hu, -⟩
    · exact hex (List.mem_reverse.mp (heq ▸ hnw))
    · exact hu.1 hnw
  have hexnotin : Gc.edge x ∉ rc.map Gc.edge := by
    intro hm
    obtain ⟨w, hwrc, hw⟩ := List.mem_map.mp hm
    rw [Gc.edge.injective hw] at hwrc
    exact hx hwrc
  have hdEex : Gc.DiskE (rc.map Gc.edge) (Gc.edge x) := ⟨hdNex, hexnotin⟩
  have hdEx : Gc.DiskE (rc.map Gc.edge) x := (diskE_edge_iff hplan hUerc).mp hdEex
  obtain ⟨w, hw⟩ := exists_diskF_chordRing hemb hbex hbeex hdEex
  have hkw : Gc.Kernel rc w :=
    (diskF_chordRing_eq_kernel hemb hpre hbex hbeex hdEex w).mp hw
  refine ((diskF_chordRing hplan hplain hbridge hconn hUerc hperc hdEex hbex hbeex).mp
    hw).2 ?_
  rw [hplain.edge_edge]
  exact (diskF_chordRing_eq_kernel hemb hpre hbx hbex hdEx w).mpr hkw


/-! ### Counting the darts of a face that point at the perimeter

A face outside the kernel meets the perimeter band in exactly two of its darts,
so the arity bound on the perimeter faces bounds the darts of such a face that
point into the kernel. -/

omit [Finite Dm] in
/-- **A face outside the kernel has exactly two darts whose E-link meets the
perimeter.**  This is the reference's `fcard_adj_perimeter`. -/
theorem fcard_adj_perimeter (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} (hx : ¬ Gc.Kernel rc x) :
    {z : Dc | Gc.CFace x z ∧ Gc.Fband rc (Gc.edge z)}.ncard = 2 := by
  classical
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hbx : Gc.Fband rc x := by by_contra hb; exact hx hb
  obtain ⟨y, hyrc, hxy⟩ := hbx
  have hnyrc : Gc.node y ∈ rc := (node_mem_ring_iff hemb y).mpr hyrc
  have hfey : Gc.face (Gc.edge y) ∈ rc := by
    rw [← node_mem_ring_iff hemb, Gc.edgeK y]; exact hyrc
  have hbey : Gc.Fband rc (Gc.edge y) := ⟨Gc.face (Gc.edge y), hfey, Gc.cface_face _⟩
  have hceny : Gc.CFace (Gc.edge (Gc.node y)) y := by
    have h0 := Gc.cface_face (Gc.edge (Gc.node y))
    rw [Gc.nodeK y] at h0
    exact h0
  have hxeny : Gc.CFace x (Gc.edge (Gc.node y)) := hxy.trans hceny.symm
  have hbeeny : Gc.Fband rc (Gc.edge (Gc.edge (Gc.node y))) := by
    rw [hplain.edge_edge]
    exact ⟨Gc.node y, hnyrc, SameCycle.refl _ _⟩
  have hne : Gc.edge (Gc.node y) ≠ y := by
    intro heq
    rcases edge_perimeter hemb (Gc.node y) with hp | hp
    · exact hp hnyrc
    · exact hp (by rw [heq]; exact hyrc)
  have hSeq : {z : Dc | Gc.CFace x z ∧ Gc.Fband rc (Gc.edge z)}
      = {y, Gc.edge (Gc.node y)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxz, hbez⟩
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hzy, hzeny⟩ := hcon
      have hzy' : Gc.CFace z y := hxz.symm.trans hxy
      have hbz : Gc.Fband rc z := ⟨y, hyrc, hzy'⟩
      have hzrc : z ∉ rc := fun hzr => hzy (hemb.base.simple.eq_of_cface hzr hyrc hzy')
      have hezrc : Gc.edge z ∉ rc := by
        intro hezr
        refine hzeny ?_
        have hz' : z ∈ rc.map Gc.edge := List.mem_map.mpr ⟨Gc.edge z, hezr, hplain.edge_edge z⟩
        have heny' : Gc.edge (Gc.node y) ∈ rc.map Gc.edge :=
          List.mem_map.mpr ⟨Gc.node y, hnyrc, rfl⟩
        exact (scycle_edge_ring hemb).simple.eq_of_cface hz' heny' (hzy'.trans hceny.symm)
      rcases chordless_perimeter hemb hpre hzrc hezrc with hk | hk
      · exact hk hbz
      · exact hk hbez
    · rintro (rfl | rfl)
      · exact ⟨hxy, hbey⟩
      · exact ⟨hxeny, hbeeny⟩
  rw [hSeq, Set.ncard_pair (Ne.symm hne)]

omit [Finite Dm] in
/-- The arity of a face outside the kernel splits into its two perimeter darts
and the darts pointing into the kernel. -/
private theorem arity_eq_two_add (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} (hx : ¬ Gc.Kernel rc x) :
    Gc.arity x = 2 + {z : Dc | Gc.CFace x z ∧ Gc.Kernel rc (Gc.edge z)}.ncard := by
  classical
  have hA : {z : Dc | Gc.CFace x z ∧ Gc.Fband rc (Gc.edge z)}.ncard = 2 :=
    fcard_adj_perimeter hemb hpre hx
  have hcard : {z : Dc | Gc.CFace x z}.ncard = Gc.arity x := by
    have hset : {z : Dc | Gc.CFace x z} = ↑(orbitList Gc.face x).toFinset := by
      ext z; simp [mem_orbitList]
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_orbitList _ _),
      length_orbitList]
    rfl
  have hunion : {z : Dc | Gc.CFace x z}
      = {z : Dc | Gc.CFace x z ∧ Gc.Fband rc (Gc.edge z)}
        ∪ {z : Dc | Gc.CFace x z ∧ Gc.Kernel rc (Gc.edge z)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hz
      by_cases hb : Gc.Fband rc (Gc.edge z)
      · exact Or.inl ⟨hz, hb⟩
      · exact Or.inr ⟨hz, hb⟩
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  have hdisj : Disjoint {z : Dc | Gc.CFace x z ∧ Gc.Fband rc (Gc.edge z)}
      {z : Dc | Gc.CFace x z ∧ Gc.Kernel rc (Gc.edge z)} := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hb⟩ ⟨-, hk⟩
    exact hk hb
  rw [← hcard, hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hA]

omit [Finite Dm] in
/-- **A face outside the kernel has a dart pointing into the kernel.**  This is
the reference's `adj_kernel_min`. -/
theorem adj_kernel_min (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} (hx : ¬ Gc.Kernel rc x) :
    ∃ y, Gc.Kernel rc y ∧ Gc.CFace x (Gc.edge y) := by
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have harity := arity_eq_two_add hemb hpre hx
  have hbx : Gc.Fband rc x := by by_contra hb; exact hx hb
  obtain ⟨y0, hy0rc, hxy0⟩ := hbx
  have h3 : 3 ≤ Gc.arity x := by
    rw [Gc.arity_cface hxy0]
    exact (hemb.ringArity y0 hy0rc).1
  obtain ⟨z, hz⟩ : {z : Dc | Gc.CFace x z ∧ Gc.Kernel rc (Gc.edge z)}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  refine ⟨Gc.edge z, hz.2, ?_⟩
  rw [hplain.edge_edge]
  exact hz.1

omit [Finite Dm] in
/-- **A face outside the kernel has at most four darts pointing into the
kernel.**  This is the reference's `adj_kernel_max`. -/
theorem adj_kernel_max (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} (hx : ¬ Gc.Kernel rc x) :
    {z : Dc | Gc.CFace x z ∧ Gc.Kernel rc (Gc.edge z)}.ncard ≤ 4 := by
  have harity := arity_eq_two_add hemb hpre hx
  have hbx : Gc.Fband rc x := by by_contra hb; exact hx hb
  obtain ⟨y0, hy0rc, hxy0⟩ := hbx
  have h6 : Gc.arity x ≤ 6 := by
    rw [Gc.arity_cface hxy0]
    exact (hemb.ringArity y0 hy0rc).2
  omega


/-! ### The shape of the extension

Every dart off the perimeter is accounted for by the kernel in one of four
ways, which is what makes the four-case definition of the embedding total. -/

omit [Finite Dm] in
/-- **Four cases cover every dart.**  This is the reference's `embed_cases`. -/
theorem embed_cases (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (x : Dc) :
    (Gc.Kernel rc x ∨ Gc.Kernel rc (Gc.edge x)) ∨
      Gc.Kernel rc (Gc.node x) ∨ Gc.Kernel rc (Gc.node (Gc.edge x)) := by
  have hplain : Gc.Plain := hemb.base.base.base.base.plain
  have hin : ∀ w : Dc, w ∉ rc →
      (Gc.Kernel rc w ∨ Gc.Kernel rc (Gc.edge w)) ∨ Gc.Kernel rc (Gc.node w) := by
    intro w hw
    by_cases hew : Gc.edge w ∈ rc
    · by_cases hnw : Gc.edge (Gc.node w) ∈ rc
      · -- both E-links land on the perimeter, so the face of `w` has two darts
        exfalso
        have hfw : Gc.face w ∈ rc := by
          rw [← node_mem_ring_iff hemb, hplain.node_face]
          exact hew
        have h0 : Gc.CFace (Gc.edge (Gc.node w)) w := by
          have h1 := Gc.cface_face (Gc.edge (Gc.node w))
          rw [Gc.nodeK w] at h1
          exact h1
        have hD : Gc.face w = Gc.edge (Gc.node w) :=
          hemb.base.simple.eq_of_cface hfw hnw (h0.trans (Gc.cface_face w)).symm
        have hff : Gc.face (Gc.face w) = w := by rw [hD]; exact Gc.nodeK w
        have h2 : Gc.arity w ≤ 2 := arity_le_two hff
        have h3 : 3 ≤ Gc.arity (Gc.face w) := (hemb.ringArity (Gc.face w) hfw).1
        rw [Gc.arity_face w] at h3
        omega
      · have hnwrc : Gc.node w ∉ rc := fun hc => hw ((node_mem_ring_iff hemb w).mp hc)
        rcases chordless_perimeter hemb hpre hnwrc hnw with hk | hk
        · exact Or.inr hk
        · have h0 : Gc.CFace (Gc.edge (Gc.node w)) w := by
            have h1 := Gc.cface_face (Gc.edge (Gc.node w))
            rw [Gc.nodeK w] at h1
            exact h1
          exact Or.inl (Or.inl ((Kernel.congr h0).mp hk))
    · exact Or.inl (chordless_perimeter hemb hpre hw hew)
  rcases edge_perimeter hemb x with hx | hex
  · rcases hin x hx with hres | hres
    · exact Or.inl hres
    · exact Or.inr (Or.inl hres)
  · rcases hin (Gc.edge x) hex with hres | hres
    · rcases hres with hres | hres
      · exact Or.inl (Or.inr hres)
      · rw [hplain.edge_edge] at hres
        exact Or.inl (Or.inl hres)
    · exact Or.inr (Or.inr hres)

open scoped Classical in
/-- The extension of the preembedding `h` to every dart off the perimeter: on
the kernel it is `h` itself, and elsewhere it is read off the kernel dart that
`Hypermap.embed_cases` provides. -/
noncomputable def embed (Gc : Hypermap Dc) (Gm : Hypermap Dm) (rc : List Dc)
    (h : Dc → Dm) (x : Dc) : Dm :=
  if Gc.Kernel rc x then h x
  else if Gc.Kernel rc (Gc.edge x) then Gm.edge (h (Gc.edge x))
  else if Gc.Kernel rc (Gc.node x) then Gm.face (Gm.edge (h (Gc.node x)))
  else Gm.edge (Gm.node (Gm.node (h (Gc.node (Gc.edge x)))))

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- On the kernel the embedding is the preembedding. -/
@[simp] theorem embed_of_kernel {x : Dc} (hx : Gc.Kernel rc x) :
    embed Gc Gm rc h x = h x := by
  rw [embed]
  split_ifs
  rfl

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- One E-step off the kernel, the embedding is the E-link of the
preembedding. -/
theorem embed_of_kernel_edge {x : Dc} (hx : ¬ Gc.Kernel rc x)
    (hex : Gc.Kernel rc (Gc.edge x)) : embed Gc Gm rc h x = Gm.edge (h (Gc.edge x)) := by
  rw [embed]
  split_ifs
  rfl

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- One N-step off the kernel, the embedding is one F-step past the E-link of
the preembedding. -/
theorem embed_of_kernel_node {x : Dc} (hx : ¬ Gc.Kernel rc x)
    (hex : ¬ Gc.Kernel rc (Gc.edge x)) (hnx : Gc.Kernel rc (Gc.node x)) :
    embed Gc Gm rc h x = Gm.face (Gm.edge (h (Gc.node x))) := by
  rw [embed]
  split_ifs
  rfl

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- In the remaining case the embedding is read off the kernel dart
`node (edge x)`. -/
theorem embed_of_kernel_node_edge {x : Dc} (hx : ¬ Gc.Kernel rc x)
    (hex : ¬ Gc.Kernel rc (Gc.edge x)) (hnx : ¬ Gc.Kernel rc (Gc.node x)) :
    embed Gc Gm rc h x = Gm.edge (Gm.node (Gm.node (h (Gc.node (Gc.edge x))))) := by
  rw [embed]
  split_ifs
  rfl


end Chordless

/-! ### Functoriality of the preembedding

The preembedding commutes with `edge` everywhere on the kernel.  This is the
reference's `embed_functor`, and it is the gate to the whole embedding
construction.  A failure of commutation is turned into a face-simple R-cycle
whose head is not edge-central, whose other darts are, and whose disk lies in
the kernel; such a cycle is then cut down along a chord until its disk becomes
too small, which is the induction that occupies most of this section. -/

section Functor

/-- Splitting a list at its first dart that satisfies a predicate. -/
private theorem exists_first_split {α : Type*} (P : α → Prop) (l : List α) :
    (∀ z ∈ l, ¬ P z) ∨ ∃ a w b, l = a ++ w :: b ∧ (∀ z ∈ a, ¬ P z) ∧ P w := by
  classical
  induction l with
  | nil => exact Or.inl (by simp)
  | cons c t ih =>
    by_cases hc : P c
    · exact Or.inr ⟨[], c, t, rfl, by simp, hc⟩
    · rcases ih with hall | ⟨a, w, b, hab, ha, hw⟩
      · refine Or.inl fun z hz => ?_
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hc
        · exact hall z hz
      · refine Or.inr ⟨c :: a, w, b, by rw [hab]; rfl, fun z hz => ?_, hw⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hc
        · exact ha z hz

/-- A list is empty, a singleton, or has at least two darts. -/
private theorem list_cases_length {α : Type*} (l : List α) :
    l = [] ∨ (∃ y, l = [y]) ∨ 2 ≤ l.length := by
  match l with
  | [] => exact Or.inl rfl
  | [y] => exact Or.inr (Or.inl ⟨y, rfl⟩)
  | _ :: _ :: _ => exact Or.inr (Or.inr (by simp only [List.length_cons]; omega))

/-- The default of `List.getLastD` is not used on a nonempty list. -/
private theorem getLastD_mem {α : Type*} :
    ∀ (l : List α) (d : α), l ≠ [] → l.getLastD d ∈ l := by
  intro l
  induction l with
  | nil => intro d hl; exact absurd rfl hl
  | cons a t ih =>
    intro d _
    rw [List.getLastD_cons]
    rcases t with _ | ⟨b, t'⟩
    · simp
    · exact List.mem_cons_of_mem _ (ih a (by simp))

/-- A cyclic chain gives a chain that returns to its head. -/
private theorem isChain_cons_concat {α : Type*} {e : α → α → Prop} {x : α} {t : List α}
    (hc : IsCyclicChain e (x :: t)) : List.IsChain e (x :: (t ++ [x])) := by
  rw [← List.cons_append]
  refine hc.isChain.append (List.isChain_singleton x) ?_
  intro a ha b hb
  rw [Option.mem_def, List.getLast?_eq_some_getLast (List.cons_ne_nil x t),
    Option.some.injEq] at ha
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  subst ha; subst hb
  exact (isCyclicChain_cons.mp hc).2

/-- Following an R-link chain forward out of the disk of a ring stays strictly
inside the disk, as long as the chain avoids the face band of the ring. -/
private theorem diskF_mem_of_rlink (q : List Dc) :
    ∀ (L : List Dc) (u : Dc), List.IsChain Gc.Rlink (u :: L) →
      (∀ z ∈ L, ¬ Gc.Fband q z) → Gc.DiskN q u → ∀ z ∈ L, Gc.DiskF q z := by
  intro L
  induction L with
  | nil => intro u _ _ _ z hz; exact absurd hz (by simp)
  | cons v L ih =>
    intro u hchain hband hu
    have hlink : Gc.Rlink u v := (List.isChain_cons_cons.mp hchain).1
    have htail : List.IsChain Gc.Rlink (v :: L) := (List.isChain_cons_cons.mp hchain).2
    have hbv : ¬ Gc.Fband q v := hband v List.mem_cons_self
    have hcf : Gc.CFace (Gc.face (Gc.edge u)) v :=
      (Gc.cface_face (Gc.edge u)).symm.trans hlink
    have hdn : Gc.DiskN q (Gc.face (Gc.edge u)) :=
      diskN_node_iff.mp (by rw [Gc.edgeK u]; exact hu)
    have hdfv : Gc.DiskF q v :=
      (diskF_congr hcf).mp ⟨hdn, fun hb => hbv ((Fband.congr hcf).mp hb)⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hdfv
    · exact ih v htail (fun t ht => hband t (List.mem_cons_of_mem _ ht)) hdfv.1 z hz

/-- Following an R-link chain backward into the disk of a ring: if the far end
is in the disk and the chain avoids the face band of the ring, so is the near
end. -/
private theorem diskN_head_rlink (q : List Dc) :
    ∀ (L : List Dc) (u : Dc), List.IsChain Gc.Rlink (u :: L) →
      (∀ z ∈ L, ¬ Gc.Fband q z) → Gc.DiskN q (L.getLastD u) → Gc.DiskN q u := by
  intro L
  induction L with
  | nil => intro u _ _ hu; exact hu
  | cons v L ih =>
    intro u hchain hband hlast
    have hlink : Gc.Rlink u v := (List.isChain_cons_cons.mp hchain).1
    have htail : List.IsChain Gc.Rlink (v :: L) := (List.isChain_cons_cons.mp hchain).2
    rw [List.getLastD_cons] at hlast
    have hv : Gc.DiskN q v :=
      ih v htail (fun t ht => hband t (List.mem_cons_of_mem _ ht)) hlast
    have hbv : ¬ Gc.Fband q v := hband v List.mem_cons_self
    have hcf : Gc.CFace (Gc.face (Gc.edge u)) v :=
      (Gc.cface_face (Gc.edge u)).symm.trans hlink
    have hdf : Gc.DiskF q (Gc.face (Gc.edge u)) := (diskF_congr hcf).mpr ⟨hv, hbv⟩
    have hnd := diskN_node_iff.mpr hdf.1
    rwa [Gc.edgeK u] at hnd

/-- The disk of a ring only depends on the node of a dart. -/
private theorem diskN_congr_cnode {s : List Dc} {u v : Dc} (huv : Gc.CNode u v) :
    Gc.DiskN s u ↔ Gc.DiskN s v := by
  replace huv := (sameCycle_iff_reflTransGen Gc.node u v).mp huv
  induction huv with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (by rw [hbc]; exact diskN_node_iff.symm)

/-- **Monotonicity of disks.**  If every dart of `q` lies in the disk of `s`,
and the contour exploration of the disk of `q` never reaches `s` from inside,
then the disk of `q` is contained in the disk of `s`. -/
private theorem diskN_mono {s q : List Dc} (hq : ∀ w ∈ q, Gc.DiskN s w)
    (hstep : ∀ y, Gc.DiskN s y → Gc.DiskN q y → y ∉ q → y ∉ s) :
    ∀ z, Gc.DiskN q z → Gc.DiskN s z := by
  have key : ∀ u v : Dc, Relation.ReflTransGen (Gc.DLink q) u v →
      Gc.DiskN s u ∧ Gc.DiskN q u → Gc.DiskN s v ∧ Gc.DiskN q v := by
    intro u v huv
    induction huv with
    | refl => exact id
    | @tail b c _ hbc ih =>
      intro hu
      obtain ⟨hsb, hqb⟩ := ih hu
      obtain ⟨hbq, hclink⟩ := hbc
      have hqc : Gc.DiskN q c := by
        obtain ⟨t, ht, hpath⟩ := hqb
        exact ⟨t, ht, hpath.tail ⟨hbq, hclink⟩⟩
      refine ⟨?_, hqc⟩
      rcases hclink with hcl | hcl
      · exact diskN_node_iff.mp (by rw [← hcl]; exact hsb)
      · subst hcl
        exact diskN_face hsb (hstep b hsb hqb hbq)
  rintro z ⟨w, hw, hpath⟩
  exact (key _ _ hpath ⟨diskN_nodeInv (hq w hw), diskN_nodeInv (diskN_of_mem hw)⟩).1

omit [Finite Dm] in
/-- The base case of the `embed_functor` induction: if both `node x` and
`node (node x)` are edge-central and the whole node of `x` lies in the kernel,
then so is `x` itself. -/
private theorem functor_base (hqc : Gc.Quasicubic rc) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} {p : List Dc}
    (hdN_ac : ∀ z, Gc.DiskN (x :: p) z → Gc.Kernel rc z)
    (hnx : EdgeCentral Gc Gm h (Gc.node x))
    (hnnx : EdgeCentral Gc Gm h (Gc.node (Gc.node x))) :
    EdgeCentral Gc Gm h x := by
  have hnx' : h (Gc.edge (Gc.node x)) = Gm.edge (h (Gc.node x)) := hnx
  have hnnx' : h (Gc.edge (Gc.node (Gc.node x))) = Gm.edge (h (Gc.node (Gc.node x))) := hnnx
  have hdNx : Gc.DiskN (x :: p) x := diskN_of_mem List.mem_cons_self
  have hdNnx : Gc.DiskN (x :: p) (Gc.node x) := diskN_node hdNx
  have hdNnnx : Gc.DiskN (x :: p) (Gc.node (Gc.node x)) := diskN_node hdNnx
  have hkx : Gc.Kernel rc x := hdN_ac x hdNx
  have hknx : Gc.Kernel rc (Gc.node x) := hdN_ac _ hdNnx
  have hknnx : Gc.Kernel rc (Gc.node (Gc.node x)) := hdN_ac _ hdNnnx
  have hxbc : x ∉ rc := not_mem_of_kernel hkx
  have hn3x : Gc.node (Gc.node (Gc.node x)) = x := hqc.node_node_node hxbc
  have hfe_x : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
    have hk := Gc.nodeK (Gc.node (Gc.node x))
    rwa [hn3x] at hk
  have hfe_m : ∀ u : Dm, Gm.face (Gm.edge u) = Gm.node (Gm.node u) := by
    intro u
    have hk := Gm.nodeK (Gm.node (Gm.node u))
    rwa [hcubm.node_node_node u] at hk
  have hker_enx : Gc.edge (Gc.node x) ∈ {z : Dc | Gc.Kernel rc z} := by
    change Gc.Kernel rc (Gc.edge (Gc.node x))
    rw [← kernel_face, Gc.nodeK x]
    exact hkx
  have hker_ennx : Gc.edge (Gc.node (Gc.node x)) ∈ {z : Dc | Gc.Kernel rc z} := by
    change Gc.Kernel rc (Gc.edge (Gc.node (Gc.node x)))
    rw [← kernel_face, Gc.nodeK (Gc.node x)]
    exact hknx
  have hker_ex : Gc.edge x ∈ {z : Dc | Gc.Kernel rc z} := by
    change Gc.Kernel rc (Gc.edge x)
    rw [← kernel_face, hfe_x]
    exact hknnx
  have e1 : h x = Gm.node (Gm.node (h (Gc.node x))) := by
    have h1 := hpre.face _ hker_enx
    rw [Gc.nodeK x, hnx', hfe_m] at h1
    exact h1
  have e2 : h (Gc.node x) = Gm.node (Gm.node (h (Gc.node (Gc.node x)))) := by
    have h1 := hpre.face _ hker_ennx
    rw [Gc.nodeK (Gc.node x), hnnx', hfe_m] at h1
    exact h1
  have e3 : h (Gc.node (Gc.node x)) = Gm.face (h (Gc.edge x)) := by
    have h1 := hpre.face _ hker_ex
    rw [hfe_x] at h1
    exact h1
  have hnhx : h (Gc.node x) = Gm.node (h x) := by
    rw [e1, hcubm.node_node_node]
  have hnode : Gm.node (h (Gc.node x)) = h (Gc.node (Gc.node x)) := by
    rw [e2, hcubm.node_node_node]
  have hnnhx : h (Gc.node (Gc.node x)) = Gm.node (Gm.node (h x)) := by
    rw [← hnode, hnhx]
  change h (Gc.edge x) = Gm.edge (h x)
  refine Gm.face.injective ?_
  rw [← e3, hnnhx, hfe_m]

omit [Finite Dm] in
/-- The induction step of `embed_functor` in the case where `node x` is
edge-central but `node (node x)` is not: the chord `edge (node (node x))` cuts a
strictly smaller ring out of the R-cycle. -/
private theorem functor_step_node (hplanc : Gc.Planar) (hplainc : Gc.Plain)
    (hbridgec : Gc.Bridgeless) (hqc : Gc.Quasicubic rc) (hplainm : Gm.Plain)
    {x : Dc} {p : List Dc} (hURp : Gc.Scycle Gc.Rlink (x :: p))
    (hp_hc : ∀ z ∈ p, EdgeCentral Gc Gm h z)
    (hdN_ac : ∀ z, Gc.DiskN (x :: p) z → Gc.Kernel rc z)
    (hnx : EdgeCentral Gc Gm h (Gc.node x))
    (hnnx : ¬ EdgeCentral Gc Gm h (Gc.node (Gc.node x)))
    (ih : ∀ (x' : Dc) (p' : List Dc),
      {z : Dc | Gc.DiskN (x' :: p') z}.ncard < {z : Dc | Gc.DiskN (x :: p) z}.ncard →
      ¬ EdgeCentral Gc Gm h x' → Gc.Scycle Gc.Rlink (x' :: p') →
      (∀ z ∈ p', EdgeCentral Gc Gm h z) →
      (∀ z, Gc.DiskN (x' :: p') z → Gc.Kernel rc z) → False) :
    False := by
  classical
  have hsimple : Gc.Simple (x :: p) := hURp.simple
  have hnodup : (x :: p).Nodup := hURp.nodup
  have hcyc : IsCyclicChain Gc.Rlink (x :: p) := hURp.isCyclicChain
  have hdNx : Gc.DiskN (x :: p) x := diskN_of_mem List.mem_cons_self
  have hdNnx : Gc.DiskN (x :: p) (Gc.node x) := diskN_node hdNx
  have hdNnnx : Gc.DiskN (x :: p) (Gc.node (Gc.node x)) := diskN_node hdNnx
  have hxbc : x ∉ rc := not_mem_of_kernel (hdN_ac x hdNx)
  have hn3x : Gc.node (Gc.node (Gc.node x)) = x := hqc.node_node_node hxbc
  have hnxne : Gc.node x ≠ x := hqc.node_ne hxbc
  have hfe_x : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
    have hk := Gc.nodeK (Gc.node (Gc.node x))
    rwa [hn3x] at hk
  obtain ⟨enx, henx⟩ : ∃ t : Dc, t = Gc.edge (Gc.node x) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ t : Dc, t = Gc.edge (Gc.node (Gc.node x)) := ⟨_, rfl⟩
  have hface_enx : Gc.face enx = x := by rw [henx]; exact Gc.nodeK x
  have hface_c : Gc.face c = Gc.node x := by rw [hcdef]; exact Gc.nodeK (Gc.node x)
  have hedge_enx : Gc.edge enx = Gc.node x := by rw [henx]; exact hplainc.edge_edge _
  have hedge_c : Gc.edge c = Gc.node (Gc.node x) := by rw [hcdef]; exact hplainc.edge_edge _
  have hcf_x_enx : Gc.CFace x enx := by
    have h0 := Gc.cface_face enx
    rw [hface_enx] at h0
    exact h0.symm
  have hcf_c_nx : Gc.CFace c (Gc.node x) := by
    have h0 := Gc.cface_face c
    rwa [hface_c] at h0
  have hnotfb_p_x : ¬ Gc.Fband p x := hsimple.not_fband
  have hnotfb_p_enx : ¬ Gc.Fband p enx := fun hb => hnotfb_p_x ((Fband.congr hcf_x_enx).mpr hb)
  have hsimple_p : Gc.Simple p := hsimple.of_cons
  have hsimple_p1 : Gc.Simple (p ++ [enx]) := simple_concat.mpr ⟨hnotfb_p_enx, hsimple_p⟩
  have hlast_link : Gc.Rlink ((x :: p).getLast (List.cons_ne_nil x p)) x :=
    (isCyclicChain_cons.mp hcyc).2
  have hchain_xp1 : List.IsChain Gc.Rlink (x :: (p ++ [enx])) := by
    have h0 : x :: (p ++ [enx]) = (x :: p) ++ [enx] := by simp
    rw [h0]
    refine hcyc.isChain.append (List.isChain_singleton enx) ?_
    intro u hu v hv
    rw [Option.mem_def, List.getLast?_eq_some_getLast (List.cons_ne_nil x p),
      Option.some.injEq] at hu
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
    subst hu; subst hv
    exact hlast_link.trans hcf_x_enx
  have hrl_enx_c : Gc.Rlink enx c := by
    change Gc.CFace (Gc.edge enx) c
    rw [hedge_enx]
    exact hcf_c_nx.symm
  have hrl_xc : ∀ y : Dc, Gc.Rlink x y ↔ Gc.Rlink c y := by
    intro y
    have h1 : Gc.CFace (Gc.edge x) (Gc.edge c) := by
      rw [hedge_c, ← hfe_x]
      exact Gc.cface_face _
    exact ⟨fun hy => h1.symm.trans hy, fun hy => h1.trans hy⟩
  have hchain_c : List.IsChain Gc.Rlink (c :: (p ++ [enx] ++ [c])) := by
    have h0 : x :: (p ++ [enx] ++ [c]) = (x :: (p ++ [enx])) ++ [c] := by simp
    have h1 : List.IsChain Gc.Rlink (x :: (p ++ [enx] ++ [c])) := by
      rw [h0]
      refine hchain_xp1.append (List.isChain_singleton c) ?_
      intro u hu v hv
      rw [Option.mem_def,
        List.getLast?_eq_some_getLast (List.cons_ne_nil x (p ++ [enx])),
        Option.some.injEq] at hu
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hu; subst hv
      have hgl : (x :: (p ++ [enx])).getLast (List.cons_ne_nil x (p ++ [enx])) = enx := by
        simp
      rw [hgl]
      exact hrl_enx_c
    exact h1.imp_head (fun {z} hz => (hrl_xc z).mp hz)
  obtain ⟨a, w, b, hab, ha, hw⟩ :
      ∃ a w b, p ++ [enx] ++ [c] = a ++ w :: b ∧ (∀ z ∈ a, ¬ Gc.CFace c z) ∧ Gc.CFace c w := by
    rcases exists_first_split (fun z => Gc.CFace c z) (p ++ [enx] ++ [c]) with hall | hres
    · exact absurd (Equiv.Perm.SameCycle.refl Gc.face c) (hall c (by simp))
    · exact hres
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = a.length := ⟨_, rfl⟩
  have halen : k ≤ (p ++ [enx]).length := by
    have hlen_ab := congrArg List.length hab
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen_ab ⊢
    omega
  have ha_take : (p ++ [enx]).take k = a := by
    have h1 : ((p ++ [enx]) ++ [c]).take k = a := by
      rw [hab, hk]; exact List.take_left' rfl
    rw [← h1, List.take_append_of_le_length halen]
  have hsub_a : ∀ z ∈ a, z ∈ p ∨ z = enx := by
    intro z hz
    rw [← ha_take] at hz
    have h2 : z ∈ p ++ [enx] := List.mem_of_mem_take hz
    simpa using h2
  have hsimple_a : Gc.Simple a := by
    rw [← ha_take]
    have h2 : Gc.Simple ((p ++ [enx]).take k ++ (p ++ [enx]).drop k) := by
      rw [List.take_append_drop]; exact hsimple_p1
    exact (simple_append.mp h2).1
  have hnotfb_a_c : ¬ Gc.Fband a c := by
    rintro ⟨z, hz, hcz⟩
    exact ha z hz hcz
  have hqsimple : Gc.Simple (c :: a) := simple_cons.mpr ⟨hnotfb_a_c, hsimple_a⟩
  have hchain_ca : List.IsChain Gc.Rlink (c :: a) := by
    have h1 : List.IsChain Gc.Rlink (c :: (a ++ w :: b)) := by rw [← hab]; exact hchain_c
    exact h1.prefix ⟨w :: b, by simp⟩
  have hqcyc : IsCyclicChain Gc.Rlink (c :: a) := by
    refine isCyclicChain_cons.mpr ⟨hchain_ca, ?_⟩
    have h2 : List.IsChain Gc.Rlink ((c :: a) ++ (w :: b)) := by
      have h3 : (c :: a) ++ (w :: b) = c :: (a ++ w :: b) := by simp
      rw [h3, ← hab]
      exact hchain_c
    have hlink := h2.rel_getLast_head_of_append (by simp) (by simp)
    simp only [List.head_cons] at hlink
    exact hlink.trans hw.symm
  have hqScycle : Gc.Scycle Gc.Rlink (c :: a) := ⟨hqcyc, hqsimple⟩
  have hcnothc : ¬ EdgeCentral Gc Gm h c := by
    rw [hcdef]
    intro hcon
    exact hnnx ((edgeCentral_edge hplainc hplainm _).mp hcon)
  have hq_hc : ∀ z ∈ a, EdgeCentral Gc Gm h z := by
    intro z hz
    rcases hsub_a z hz with hzp | rfl
    · exact hp_hc z hzp
    · rw [henx]
      exact (edgeCentral_edge hplainc hplainm _).mpr hnx
  have hq_proper : Gc.ProperRing (c :: a) := by
    rcases list_cases_length a with hnil | ⟨x1, h1⟩ | hlen
    · exfalso
      rw [hnil] at hqScycle
      have hl : Gc.Rlink c c := by simpa using hqScycle.isCyclicChain
      exact hbridgec c hl.symm
    · rw [h1]
      simp only [properRing_pair]
      intro hcon
      refine hnnx ?_
      rw [← hedge_c, hcon]
      exact hq_hc x1 (by rw [h1]; exact List.mem_cons_self)
    · refine Gc.properRing_of_two_lt_length ?_
      simp only [List.length_cons]
      omega
  have hq_notdNx : ¬ Gc.DiskN (c :: a) x := by
    have h1 : ¬ Gc.DiskN (c :: a) (Gc.edge c) :=
      diskN_edge_ring hplanc hplainc hqScycle hq_proper List.mem_cons_self
    intro hcon
    refine h1 ?_
    rw [hedge_c]
    exact diskN_node (diskN_node hcon)
  have hnnx_ne : Gc.node (Gc.node x) ≠ x := by
    intro hcon
    refine hnxne ?_
    have h1 := congrArg Gc.node hcon
    rw [hn3x] at h1
    exact h1.symm
  have hnnx_notin : Gc.node (Gc.node x) ∉ (x :: p) := by
    simp only [List.mem_cons, not_or]
    exact ⟨hnnx_ne, fun hmem => hnnx (hp_hc _ hmem)⟩
  have hdN_c : Gc.DiskN (x :: p) c := by
    rw [hcdef]
    exact ((diskE_edge_iff hplanc hURp).mpr ⟨hdNnnx, hnnx_notin⟩).1
  have hmain : (∀ z ∈ (c :: a), Gc.DiskN (x :: p) z) →
      (∀ y, Gc.DiskN (x :: p) y → Gc.DiskN (c :: a) y → y ∉ (c :: a) → y ∉ (x :: p)) →
      False := by
    intro hqsub hstep
    have hmono := diskN_mono hqsub hstep
    have hsub : {z : Dc | Gc.DiskN (c :: a) z} ⊆ {z : Dc | Gc.DiskN (x :: p) z} :=
      fun z hz => hmono z hz
    have hlt : {z : Dc | Gc.DiskN (c :: a) z}.ncard < {z : Dc | Gc.DiskN (x :: p) z}.ncard :=
      Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr ⟨x, hdNx, hq_notdNx⟩)
        (Set.toFinite _)
    exact ih c a hlt hcnothc hqScycle hq_hc (fun z hz => hdN_ac z (hmono z hz))
  by_cases hpa : ∀ z ∈ p, z ∈ a
  · have hnx_notin_p : Gc.node x ∉ p := fun hmem => ha _ (hpa _ hmem) hcf_c_nx
    have hnx_notin : Gc.node x ∉ (x :: p) := by
      simp only [List.mem_cons, not_or]
      exact ⟨hnxne, hnx_notin_p⟩
    have hdN_enx : Gc.DiskN (x :: p) enx := by
      rw [henx]
      exact ((diskE_edge_iff hplanc hURp).mpr ⟨hdNnx, hnx_notin⟩).1
    refine hmain (fun z hz => ?_) (fun y _ hdNqy hyq => ?_)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hdN_c
      · rcases hsub_a z hz with hzp | rfl
        · exact diskN_of_mem (List.mem_cons_of_mem _ hzp)
        · exact hdN_enx
    · simp only [List.mem_cons, not_or]
      exact ⟨fun hcon => hq_notdNx (hcon ▸ hdNqy),
        fun hmem => hyq (List.mem_cons_of_mem _ (hpa y hmem))⟩
  · push Not at hpa
    obtain ⟨y0, hy0p, hy0a⟩ := hpa
    have halen_lt : k < p.length := by
      by_contra hcon
      push Not at hcon
      refine hy0a ?_
      have h0 : (p ++ [enx]).take p.length = p := List.take_left' rfl
      have h1 := List.take_prefix_take_left (l := p ++ [enx]) hcon
      rw [h0, ha_take] at h1
      exact h1.sublist.subset hy0p
    have ha_prefix : p = a ++ p.drop k := by
      have h1 : p.take k = a := by
        rw [← ha_take, List.take_append_of_le_length (le_of_lt halen_lt)]
      conv_lhs => rw [← List.take_append_drop k p]
      rw [h1]
    have hdrop_ne : p.drop k ≠ [] := by
      intro hcon
      have h1 : (p.drop k).length = 0 := by rw [hcon]; rfl
      rw [List.length_drop] at h1
      omega
    obtain ⟨w', e, hwe⟩ : ∃ w' e, p.drop k = w' :: e := by
      cases hd : p.drop k with
      | nil => exact absurd hd hdrop_ne
      | cons w' e => exact ⟨w', e, rfl⟩
    have hp_split0 : p = a ++ w' :: e := by rw [← hwe]; exact ha_prefix
    have hww : w = w' := by
      have h1 : a ++ w :: b = a ++ w' :: (e ++ [enx] ++ [c]) := by
        rw [← hab, hp_split0]; simp
      exact (List.cons.inj (List.append_cancel_left h1)).1
    have hp_split : p = a ++ w :: e := by rw [hww]; exact hp_split0
    have hw_mem_p : w ∈ p := by
      rw [hp_split]; exact List.mem_append_right _ List.mem_cons_self
    have hsub_a_p : ∀ z ∈ a, z ∈ p := by
      intro z hz
      rw [hp_split]
      exact List.mem_append_left _ hz
    have hchain_cycle : List.IsChain Gc.Rlink (x :: (p ++ [x])) := isChain_cons_concat hcyc
    refine hmain (fun z hz => ?_) (fun y _ hdNqy hyq => ?_)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hdN_c
      · exact diskN_of_mem (List.mem_cons_of_mem _ (hsub_a_p z hz))
    · simp only [List.mem_cons, not_or]
      refine ⟨fun hcon => hq_notdNx (hcon ▸ hdNqy), fun hyp => ?_⟩
      have hya : y ∉ a := fun hmem => hyq (List.mem_cons_of_mem _ hmem)
      have hy_tail : y ∈ w :: e := by
        rw [hp_split] at hyp
        rcases List.mem_append.mp hyp with hmem | hmem
        · exact absurd hmem hya
        · exact hmem
      obtain ⟨f, g, hfg⟩ := List.append_of_mem hy_tail
      have hp_split2 : p = a ++ f ++ y :: g := by rw [hp_split, hfg]; simp
      have hw_mem_fy : w ∈ f ++ [y] := by
        cases f with
        | nil =>
          simp only [List.nil_append] at hfg
          simp [(List.cons.inj hfg).1]
        | cons v f' =>
          simp only [List.cons_append, List.cons.injEq] at hfg
          simp [hfg.1]
      have hnodup2 : (x :: (a ++ f ++ y :: g)).Nodup := by rw [← hp_split2]; exact hnodup
      have hperm : (x :: (a ++ f ++ y :: g)).Perm ((a ++ f ++ [y]) ++ (g ++ [x])) := by
        have h1 : (a ++ f ++ [y]) ++ (g ++ [x]) = (a ++ f ++ y :: g) ++ [x] := by simp
        rw [h1]
        exact List.perm_append_comm (l₁ := [x]) (l₂ := a ++ f ++ y :: g)
      have hnodupL : ((a ++ f ++ [y]) ++ (g ++ [x])).Nodup := hperm.nodup_iff.mp hnodup2
      obtain ⟨-, -, hdisj0⟩ := List.nodup_append.mp hnodupL
      have hband : ∀ z ∈ (g ++ [x]), ¬ Gc.Fband (c :: a) z := by
        intro z hz hbz
        have hz_xp : z ∈ (x :: p) := by
          rcases List.mem_append.mp hz with hzg | hzx
          · rw [hp_split2]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hzg))
          · simp only [List.mem_singleton] at hzx
            rw [hzx]
            exact List.mem_cons_self
        rcases fband_cons.mp hbz with hzc | ⟨t, ht, hzt⟩
        · have hzw : Gc.CFace z w := hzc.trans hw
          have hw_xp : w ∈ (x :: p) := List.mem_cons_of_mem _ hw_mem_p
          have hw_L1 : w ∈ a ++ f ++ [y] := by
            rcases List.mem_append.mp hw_mem_fy with hm | hm
            · exact List.mem_append_left _ (List.mem_append_right _ hm)
            · exact List.mem_append_right _ hm
          exact hdisj0 w hw_L1 z hz (hsimple.eq_of_cface hw_xp hz_xp hzw.symm)
        · have ht_xp : t ∈ (x :: p) := List.mem_cons_of_mem _ (hsub_a_p t ht)
          exact hdisj0 t (List.mem_append_left _ (List.mem_append_left _ ht)) z hz
            (hsimple.eq_of_cface ht_xp hz_xp hzt.symm)
      have hchain_y : List.IsChain Gc.Rlink (y :: (g ++ [x])) := by
        refine hchain_cycle.suffix ⟨x :: (a ++ f), ?_⟩
        rw [hp_split2]
        simp
      have hfinal := diskF_mem_of_rlink (c :: a) (g ++ [x]) y hchain_y hband hdNqy x
        (List.mem_append_right _ List.mem_cons_self)
      exact hq_notdNx hfinal.1

omit [Finite Dm] in
/-- The induction step of `embed_functor` in the case where `node x` is not
edge-central: a spoke of the preembedding out of `edge (node x)` cuts a strictly
smaller ring out of the R-cycle. -/
private theorem functor_step_edge (hplanc : Gc.Planar) (hplainc : Gc.Plain)
    (hbridgec : Gc.Bridgeless) (hqc : Gc.Quasicubic rc) (hplainm : Gm.Plain)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    {x : Dc} {p : List Dc} (hURp : Gc.Scycle Gc.Rlink (x :: p))
    (hp_hc : ∀ z ∈ p, EdgeCentral Gc Gm h z)
    (hdN_ac : ∀ z, Gc.DiskN (x :: p) z → Gc.Kernel rc z)
    (hnx : ¬ EdgeCentral Gc Gm h (Gc.node x))
    (ih : ∀ (x' : Dc) (p' : List Dc),
      {z : Dc | Gc.DiskN (x' :: p') z}.ncard < {z : Dc | Gc.DiskN (x :: p) z}.ncard →
      ¬ EdgeCentral Gc Gm h x' → Gc.Scycle Gc.Rlink (x' :: p') →
      (∀ z ∈ p', EdgeCentral Gc Gm h z) →
      (∀ z, Gc.DiskN (x' :: p') z → Gc.Kernel rc z) → False) :
    False := by
  classical
  have hsimple : Gc.Simple (x :: p) := hURp.simple
  have hcyc : IsCyclicChain Gc.Rlink (x :: p) := hURp.isCyclicChain
  have hdNx : Gc.DiskN (x :: p) x := diskN_of_mem List.mem_cons_self
  have hdNnx : Gc.DiskN (x :: p) (Gc.node x) := diskN_node hdNx
  have hxbc : x ∉ rc := not_mem_of_kernel (hdN_ac x hdNx)
  have hnxne : Gc.node x ≠ x := hqc.node_ne hxbc
  obtain ⟨enx, henx⟩ : ∃ t : Dc, t = Gc.edge (Gc.node x) := ⟨_, rfl⟩
  have hface_enx : Gc.face enx = x := by rw [henx]; exact Gc.nodeK x
  have hedge_enx : Gc.edge enx = Gc.node x := by rw [henx]; exact hplainc.edge_edge _
  have hcf_x_enx : Gc.CFace x enx := by
    have h0 := Gc.cface_face enx
    rw [hface_enx] at h0
    exact h0.symm
  have hnx_notin : Gc.node x ∉ (x :: p) := by
    simp only [List.mem_cons, not_or]
    exact ⟨hnxne, fun hmem => hnx (hp_hc _ hmem)⟩
  have hdNenx : Gc.DiskN (x :: p) enx := by
    rw [henx]
    exact ((diskE_edge_iff hplanc hURp).mpr ⟨hdNnx, hnx_notin⟩).1
  have hcenx : ¬ EdgeCentral Gc Gm h enx := by
    rw [henx]
    intro hcon
    exact hnx ((edgeCentral_edge hplainc hplainm _).mp hcon)
  have hnotfb_p_x : ¬ Gc.Fband p x := hsimple.not_fband
  have hnotfb_p_enx : ¬ Gc.Fband p enx := fun hb => hnotfb_p_x ((Fband.congr hcf_x_enx).mpr hb)
  have hsimple_p : Gc.Simple p := hsimple.of_cons
  have hsimple_p1 : Gc.Simple (p ++ [enx]) := simple_concat.mpr ⟨hnotfb_p_enx, hsimple_p⟩
  have hfb_eq : ∀ z : Dc, Gc.Fband (x :: p) z ↔ Gc.Fband (p ++ [enx]) z := by
    intro z
    rw [fband_cons, fband_concat]
    constructor
    · rintro (hz | hz)
      · exact Or.inl (hz.trans hcf_x_enx)
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl (hz.trans hcf_x_enx.symm)
      · exact Or.inr hz
  have hlast_link : Gc.Rlink ((x :: p).getLast (List.cons_ne_nil x p)) x :=
    (isCyclicChain_cons.mp hcyc).2
  have hchain_xp1 : List.IsChain Gc.Rlink (x :: (p ++ [enx])) := by
    have h0 : x :: (p ++ [enx]) = (x :: p) ++ [enx] := by simp
    rw [h0]
    refine hcyc.isChain.append (List.isChain_singleton enx) ?_
    intro u hu v hv
    rw [Option.mem_def, List.getLast?_eq_some_getLast (List.cons_ne_nil x p),
      Option.some.injEq] at hu
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
    subst hu; subst hv
    exact hlast_link.trans hcf_x_enx
  -- the spoke of the preembedding out of `edge (node x)`
  have hkA : ∀ u v : Dc, Gc.CFace u v → u ∈ {z : Dc | Gc.Kernel rc z} →
      v ∈ {z : Dc | Gc.Kernel rc z} := fun u v huv hu => (Kernel.congr huv).mp hu
  have hker_eenx : Gc.edge enx ∈ {z : Dc | Gc.Kernel rc z} := by
    change Gc.Kernel rc (Gc.edge enx)
    rw [hedge_enx]
    exact hdN_ac _ hdNnx
  have hker_enx : enx ∈ {z : Dc | Gc.Kernel rc z} := hdN_ac _ hdNenx
  obtain ⟨q1, hq1ne, hq1chain, hq1last, hq1simple, hq1mem⟩ :=
    hpre.simple_path hkA hker_eenx hker_enx
  obtain ⟨q2, v, q1', hq1split, hq2_nofb, hvfb⟩ :
      ∃ q2 v q1', q1 = q2 ++ v :: q1' ∧ (∀ z ∈ q2, ¬ Gc.Fband (p ++ [enx]) z) ∧
        Gc.Fband (p ++ [enx]) v := by
    rcases exists_first_split (fun z => Gc.Fband (p ++ [enx]) z) q1 with hall | hres
    · exact absurd (⟨enx, by simp, hq1last⟩ : Gc.Fband (p ++ [enx]) (q1.getLastD enx))
        (hall (q1.getLastD enx) (getLastD_mem q1 enx hq1ne))
    · exact hres
  obtain ⟨y, hy_mem, hcf_vy⟩ : ∃ y, y ∈ p ++ [enx] ∧ Gc.CFace v y := hvfb
  obtain ⟨p2, s, t, hps, hst⟩ : ∃ p2 s t, p = p2 ++ s ∧ s ++ [enx] = y :: t := by
    rcases List.mem_append.mp hy_mem with hyp | hye
    · obtain ⟨p2, e, hpe⟩ := List.append_of_mem hyp
      exact ⟨p2, y :: e, e ++ [enx], hpe, by simp⟩
    · simp only [List.mem_singleton] at hye
      exact ⟨p, [], [], by simp, by simp [hye]⟩
  have hp1split : p ++ [enx] = p2 ++ y :: t := by
    rw [hps, ← hst]; simp
  have hsimple_p2yt : Gc.Simple (p2 ++ y :: t) := by rw [← hp1split]; exact hsimple_p1
  have hs_sub_p : ∀ z ∈ s, z ∈ p := by
    intro z hz; rw [hps]; exact List.mem_append_right _ hz
  have hp2_sub_p : ∀ z ∈ p2, z ∈ p := by
    intro z hz; rw [hps]; exact List.mem_append_left _ hz
  have hq2_sub_q1 : ∀ z ∈ q2, z ∈ q1 := by
    intro z hz; rw [hq1split]; exact List.mem_append_left _ hz
  -- the new ring is face-simple
  have hsimple_q2 : Gc.Simple q2 := by
    rw [hq1split] at hq1simple
    exact (simple_append.mp hq1simple).1
  have hsimple_senx : Gc.Simple (s ++ [enx]) := by
    rw [hst]; exact (simple_append.mp hsimple_p2yt).2.1
  have hsimple_s : Gc.Simple s := (simple_concat.mp hsimple_senx).2
  have hnotfb_s_enx : ¬ Gc.Fband s enx := (simple_concat.mp hsimple_senx).1
  have hnotfb_q2_enx : ¬ Gc.Fband q2 enx := by
    rintro ⟨z, hz, hcz⟩
    exact hq2_nofb z hz ⟨enx, by simp, hcz.symm⟩
  have hq2_nofb_s : ∀ z ∈ q2, ¬ Gc.Fband s z := by
    intro z hz hb
    obtain ⟨u, hu, hzu⟩ := hb
    exact hq2_nofb z hz ⟨u, List.mem_append_left _ (hs_sub_p u hu), hzu⟩
  have hsimple_q : Gc.Simple (enx :: (q2 ++ s)) := by
    refine simple_cons.mpr ⟨?_, simple_append.mpr ⟨hsimple_q2, hsimple_s, hq2_nofb_s⟩⟩
    rw [fband_append]
    exact fun hb => hb.elim hnotfb_q2_enx hnotfb_s_enx
  -- the new ring is an R-cycle
  have hchain_enxq2 : List.IsChain Gc.Rlink (enx :: q2) := by
    have h1 : List.IsChain Gc.Rlink (enx :: (q2 ++ v :: q1')) := by
      rw [← hq1split]; exact hq1chain
    exact h1.prefix ⟨v :: q1', by simp⟩
  have hrl_last_y : Gc.Rlink ((enx :: q2).getLast (List.cons_ne_nil enx q2)) y := by
    have h1 : List.IsChain Gc.Rlink ((enx :: q2) ++ (v :: q1')) := by
      have h3 : (enx :: q2) ++ (v :: q1') = enx :: (q2 ++ v :: q1') := by simp
      rw [h3, ← hq1split]
      exact hq1chain
    have h2 := h1.rel_getLast_head_of_append (by simp) (by simp)
    simp only [List.head_cons] at h2
    exact h2.trans hcf_vy
  have hchain_senx : List.IsChain Gc.Rlink (s ++ [enx]) := by
    rw [hst]
    have h1 : List.IsChain Gc.Rlink (x :: (p2 ++ y :: t)) := by
      rw [← hp1split]; exact hchain_xp1
    exact h1.suffix ⟨x :: p2, by simp⟩
  have hchain_q : List.IsChain Gc.Rlink ((enx :: (q2 ++ s)) ++ [enx]) := by
    have h0 : (enx :: (q2 ++ s)) ++ [enx] = (enx :: q2) ++ (s ++ [enx]) := by simp
    rw [h0]
    refine hchain_enxq2.append hchain_senx ?_
    intro u hu z hz
    rw [Option.mem_def, List.getLast?_eq_some_getLast (List.cons_ne_nil enx q2),
      Option.some.injEq] at hu
    have hhead : (s ++ [enx]).head? = some y := by rw [hst]; rfl
    rw [hhead, Option.mem_def, Option.some.injEq] at hz
    subst hu; subst hz
    exact hrl_last_y
  have hqcyc : IsCyclicChain Gc.Rlink (enx :: (q2 ++ s)) := by
    refine isCyclicChain_cons.mpr ⟨hchain_q.left_of_append, ?_⟩
    have h2 := hchain_q.rel_getLast_head_of_append (by simp) (by simp)
    simp only [List.head_cons] at h2
    exact h2
  have hqScycle : Gc.Scycle Gc.Rlink (enx :: (q2 ++ s)) := ⟨hqcyc, hsimple_q⟩
  have hq_hc : ∀ z ∈ (q2 ++ s), EdgeCentral Gc Gm h z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (hq1mem z (hq2_sub_q1 z hz)).2
    · exact hp_hc z (hs_sub_p z hz)
  have hq_proper : Gc.ProperRing (enx :: (q2 ++ s)) := by
    rcases list_cases_length (q2 ++ s) with hnil | ⟨y2, h1⟩ | hlen
    · exfalso
      rw [hnil] at hqScycle
      have hl : Gc.Rlink enx enx := by simpa using hqScycle.isCyclicChain
      exact hbridgec enx hl.symm
    · rw [h1]
      simp only [properRing_pair]
      intro hcon
      refine hnx ?_
      rw [← hedge_enx, hcon]
      exact hq_hc y2 (by rw [h1]; exact List.mem_cons_self)
    · refine Gc.properRing_of_two_lt_length ?_
      simp only [List.length_cons]
      omega
  have hq_notdNx : ¬ Gc.DiskN (enx :: (q2 ++ s)) x := by
    have h1 : ¬ Gc.DiskN (enx :: (q2 ++ s)) (Gc.edge enx) :=
      diskN_edge_ring hplanc hplainc hqScycle hq_proper List.mem_cons_self
    intro hcon
    refine h1 ?_
    rw [hedge_enx]
    exact diskN_node hcon
  -- the new ring lies in the disk of the old one
  have hq2_nofb_xp : ∀ z ∈ q2, ¬ Gc.Fband (x :: p) z :=
    fun z hz hb => hq2_nofb z hz ((hfb_eq z).mp hb)
  have hqsub : ∀ z ∈ (enx :: (q2 ++ s)), Gc.DiskN (x :: p) z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hdNenx
    · rcases List.mem_append.mp hz with hz | hz
      · exact (diskF_mem_of_rlink (x :: p) q2 enx hchain_enxq2 hq2_nofb_xp hdNenx z hz).1
      · exact diskN_of_mem (List.mem_cons_of_mem _ (hs_sub_p z hz))
  -- no dart of the discarded arc meets the face band of the new ring
  have hq_nofb_p2 : ∀ z ∈ p2, ¬ Gc.Fband (enx :: (q2 ++ s)) z := by
    intro z hz hb
    have hyt : ¬ Gc.Fband (y :: t) z := (simple_append.mp hsimple_p2yt).2.2 z hz
    rcases fband_cons.mp hb with hzc | hb2
    · refine hyt ?_
      rw [← hst]
      exact ⟨enx, by simp, hzc⟩
    · rw [fband_append] at hb2
      rcases hb2 with hb3 | hb3
      · obtain ⟨u, hu, hzu⟩ := hb3
        exact hq2_nofb u hu
          ⟨z, List.mem_append_left _ (hp2_sub_p z hz), hzu.symm⟩
      · obtain ⟨u, hu, hzu⟩ := hb3
        refine hyt ?_
        rw [← hst]
        exact ⟨u, List.mem_append_left _ hu, hzu⟩
  have hstep : ∀ u, Gc.DiskN (x :: p) u → Gc.DiskN (enx :: (q2 ++ s)) u →
      u ∉ (enx :: (q2 ++ s)) → u ∉ (x :: p) := by
    intro u _ hdNqu huq
    simp only [List.mem_cons, not_or]
    refine ⟨fun hcon => hq_notdNx (hcon ▸ hdNqu), fun hup => ?_⟩
    have hus : u ∉ s := fun hmem => huq (List.mem_cons_of_mem _ (List.mem_append_right _ hmem))
    have hup2 : u ∈ p2 := by
      rw [hps] at hup
      rcases List.mem_append.mp hup with hmem | hmem
      · exact hmem
      · exact absurd hmem hus
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hup2
    have hp_eq : p = A ++ u :: (B ++ s) := by rw [hps, hAB]; simp
    have hchain_A : List.IsChain Gc.Rlink (x :: (A ++ [u])) := by
      refine hcyc.isChain.prefix ⟨B ++ s, ?_⟩
      rw [hp_eq]
      simp
    have hbandA : ∀ z ∈ (A ++ [u]), ¬ Gc.Fband (enx :: (q2 ++ s)) z := by
      intro z hz
      refine hq_nofb_p2 z ?_
      rw [hAB]
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_append_left _ hz
      · simp only [List.mem_singleton] at hz
        rw [hz]
        exact List.mem_append_right _ List.mem_cons_self
    refine hq_notdNx (diskN_head_rlink (enx :: (q2 ++ s)) (A ++ [u]) x hchain_A hbandA ?_)
    rw [List.getLastD_concat]
    exact hdNqu
  have hmono := diskN_mono hqsub hstep
  have hsub : {z : Dc | Gc.DiskN (enx :: (q2 ++ s)) z} ⊆ {z : Dc | Gc.DiskN (x :: p) z} :=
    fun z hz => hmono z hz
  have hlt : {z : Dc | Gc.DiskN (enx :: (q2 ++ s)) z}.ncard
      < {z : Dc | Gc.DiskN (x :: p) z}.ncard :=
    Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr ⟨x, hdNx, hq_notdNx⟩)
      (Set.toFinite _)
  exact ih enx (q2 ++ s) hlt hcenx hqScycle hq_hc (fun z hz => hdN_ac z (hmono z hz))

omit [Finite Dm] in
/-- **No face-simple R-cycle has a non-edge-central head, edge-central tail and
a disk inside the kernel.**  This is the inner induction of the reference's
`embed_functor`, on the size of the disk. -/
private theorem no_bad_ring (hplanc : Gc.Planar) (hplainc : Gc.Plain)
    (hbridgec : Gc.Bridgeless) (hqc : Gc.Quasicubic rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (n : ℕ) :
    ∀ (x : Dc) (p : List Dc), {z : Dc | Gc.DiskN (x :: p) z}.ncard ≤ n →
      ¬ EdgeCentral Gc Gm h x → Gc.Scycle Gc.Rlink (x :: p) →
      (∀ z ∈ p, EdgeCentral Gc Gm h z) →
      (∀ z, Gc.DiskN (x :: p) z → Gc.Kernel rc z) → False := by
  induction n with
  | zero =>
    intro x p hcard _ _ _ _
    have hdNx : Gc.DiskN (x :: p) x := diskN_of_mem List.mem_cons_self
    have h0 : 0 < ({z : Dc | Gc.DiskN (x :: p) z}).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, hdNx⟩
    omega
  | succ n ihn =>
    intro x p hcard hcx hURp hp_hc hdN_ac
    have ih : ∀ (x' : Dc) (p' : List Dc),
        {z : Dc | Gc.DiskN (x' :: p') z}.ncard < {z : Dc | Gc.DiskN (x :: p) z}.ncard →
        ¬ EdgeCentral Gc Gm h x' → Gc.Scycle Gc.Rlink (x' :: p') →
        (∀ z ∈ p', EdgeCentral Gc Gm h z) →
        (∀ z, Gc.DiskN (x' :: p') z → Gc.Kernel rc z) → False := by
      intro x' p' hlt
      exact ihn x' p' (by omega)
    by_cases hnx : EdgeCentral Gc Gm h (Gc.node x)
    · by_cases hnnx : EdgeCentral Gc Gm h (Gc.node (Gc.node x))
      · exact hcx (functor_base hqc hcubm hpre hdN_ac hnx hnnx)
      · exact functor_step_node hplanc hplainc hbridgec hqc hplainm hURp hp_hc hdN_ac
          hnx hnnx ih
    · exact functor_step_edge hplanc hplainc hbridgec hqc hplainm hpre hURp hp_hc hdN_ac hnx ih

omit [Finite Dm] in
/-- **No face-simple R-cycle in the kernel has a non-edge-central head and an
edge-central tail.**  This is the second reduction of the reference's
`embed_functor`: if the ring leaves the perimeter outside then its disk is in
the kernel, and otherwise the reverse ring does. -/
private theorem no_bad_kernel_ring (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    {x : Dc} {p : List Dc} (hkx : Gc.Kernel rc x) (hcx : ¬ EdgeCentral Gc Gm h x)
    (hURp : Gc.Scycle Gc.Rlink (x :: p))
    (hp : ∀ z ∈ p, Gc.Kernel rc z ∧ EdgeCentral Gc Gm h z) : False := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hplanc : Gc.Planar := hemb.base.planar
  have hbridgec : Gc.Bridgeless := hemb.base.bridgeless
  have hconnc : Gc.Connected := hemb.base.base.connected
  have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
  by_cases hcase : ∀ t ∈ rc, ¬ Gc.DiskF (x :: p) t
  · refine no_bad_ring hplanc hplainc hbridgec hqc hplainm hcubm hpre _ x p le_rfl hcx hURp
      (fun z hz => (hp z hz).2) ?_
    intro z hdNz
    by_cases hb : Gc.Fband (x :: p) z
    · obtain ⟨u, hu, hzu⟩ := hb
      have hku : Gc.Kernel rc u := by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hkx
        · exact (hp u hu).1
      exact (Kernel.congr hzu).mpr hku
    · intro hbz
      obtain ⟨t0, ht0, hzt0⟩ := hbz
      exact hcase t0 ht0 ((diskF_congr hzt0).mp ⟨hdNz, hb⟩)
  · push Not at hcase
    obtain ⟨t0, ht0rc, ht0F⟩ := hcase
    have hproperxp : Gc.ProperRing (x :: p) := by
      rcases list_cases_length p with hnil | ⟨x2, h1⟩ | hlen
      · exfalso
        rw [hnil] at hURp
        have hl : Gc.Rlink x x := by simpa using hURp.isCyclicChain
        exact hbridgec x hl.symm
      · rw [h1]
        simp only [properRing_pair]
        intro hcon
        refine hcx ((edgeCentral_edge hplainc hplainm x).mp ?_)
        rw [hcon]
        exact (hp x2 (by rw [h1]; exact List.mem_cons_self)).2
      · exact Gc.properRing_of_two_lt_length (by simp only [List.length_cons]; omega)
    have hrot : (x :: p).rotate 1 = p ++ [x] := by simp
    have hscyc2 : Gc.Scycle Gc.Rlink (p ++ [x]) := by
      rw [← hrot]; exact scycle_rotate.mpr hURp
    have hproper2 : Gc.ProperRing (p ++ [x]) := by
      rw [← hrot, properRing_rotate hplainc]; exact hproperxp
    have hrr : Gc.revRing (p ++ [x]) = Gc.edge x :: Gc.revRing p := by
      simp [revRing]
    have hdN_eq : ∀ z : Dc, Gc.DiskN (p ++ [x]) z ↔ Gc.DiskN (x :: p) z := by
      intro z; rw [← hrot]; exact diskN_rotate
    refine no_bad_ring hplanc hplainc hbridgec hqc hplainm hcubm hpre _ (Gc.edge x)
      (Gc.revRing p) le_rfl (fun hcon => hcx ((edgeCentral_edge hplainc hplainm x).mp hcon))
      ?_ ?_ ?_
    · rw [← hrr]; exact scycle_revRing hplainc hscyc2
    · intro z hz
      exact (edgeCentral_edge hplainc hplainm z).mp (hp _ ((mem_revRing hplainc).mp hz)).2
    · intro z hdNz
      rw [← hrr, diskN_revRing hplanc hplainc hconnc hscyc2 hproper2, hdN_eq] at hdNz
      intro hbz
      obtain ⟨u, hurc, hzu⟩ := hbz
      have hdFu : Gc.DiskF (x :: p) u := by
        refine ⟨?_, ?_⟩
        · have hcn : Gc.CNode t0 u := (cnode_iff_mem hemb.base.base.base.cycle ht0rc u).mpr hurc
          exact (diskN_congr_cnode hcn).mp ht0F.1
        · rintro ⟨t1, ht1, hut1⟩
          have hkt1 : Gc.Kernel rc t1 := by
            rcases List.mem_cons.mp ht1 with rfl | ht1
            · exact hkx
            · exact (hp t1 ht1).1
          exact hkt1 ⟨u, hurc, hut1.symm⟩
      exact hdNz ((diskF_congr hzu).mpr hdFu).1

omit [Finite Dm] in
/-- **The preembedding commutes with `edge` on the kernel.**  This is the
reference's `embed_functor`. -/
theorem embed_functor (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc}
    (hx : Gc.Kernel rc x) (hex : Gc.Kernel rc (Gc.edge x)) :
    h (Gc.edge x) = Gm.edge (h x) := by
  by_contra hcon
  have hcx : ¬ EdgeCentral Gc Gm h x := hcon
  have hkA : ∀ u v : Dc, Gc.CFace u v → u ∈ {z : Dc | Gc.Kernel rc z} →
      v ∈ {z : Dc | Gc.Kernel rc z} := fun u v huv hu => (Kernel.congr huv).mp hu
  obtain ⟨q, hqne, hqchain, hqlast, hqsimple, hqmem⟩ :=
    hpre.simple_path hkA (show Gc.edge x ∈ {z : Dc | Gc.Kernel rc z} from hex)
      (show x ∈ {z : Dc | Gc.Kernel rc z} from hx)
  obtain ⟨p', yy, hq⟩ : ∃ p' yy, q = p' ++ [yy] :=
    ⟨q.dropLast, q.getLast hqne, (List.dropLast_append_getLast hqne).symm⟩
  subst hq
  rw [List.getLastD_concat] at hqlast
  have hURp : Gc.Scycle Gc.Rlink (x :: p') := by
    refine ⟨?_, ?_⟩
    · refine isCyclicChain_cons.mpr ⟨hqchain.prefix ⟨[yy], by simp⟩, ?_⟩
      have h0 : (x :: p') ++ [yy] = x :: (p' ++ [yy]) := by simp
      have h1 : List.IsChain Gc.Rlink ((x :: p') ++ [yy]) := by rw [h0]; exact hqchain
      have h2 := h1.rel_getLast_head_of_append (by simp) (by simp)
      simp only [List.head_cons] at h2
      exact h2.trans hqlast
    · refine simple_cons.mpr ⟨?_, (simple_concat.mp hqsimple).2⟩
      exact fun hb => (simple_concat.mp hqsimple).1 ((Fband.congr hqlast).mpr hb)
  exact no_bad_kernel_ring hemb hplainm hcubm hpre hx hcx hURp
    (fun z hz => hqmem z (List.mem_append_left _ hz))

end Functor

/-! ### Homomorphic rings

An R-link path in the kernel whose image under the preembedding is a face-simple
R-cycle.  This is the reference's `pre_hom_ring`, the shape in which rings are
fed to the rest of the embedding construction. -/

section HomRing

omit [Finite Dm] in
/-- **The preembedding maps an R-link of the kernel to an R-link.** -/
theorem rlink_map_embed (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {u v : Dc}
    (hu : Gc.Kernel rc u) (hv : Gc.Kernel rc v) (huv : Gc.Rlink u v) :
    Gm.Rlink (h u) (h v) := by
  have heu : Gc.Kernel rc (Gc.edge u) := (Kernel.congr huv).mpr hv
  have h1 : h (Gc.edge u) = Gm.edge (h u) := embed_functor hemb hplainm hcubm hpre hu heu
  have h2 : Gm.CFace (h (Gc.edge u)) (h v) := cface_h hpre heu huv
  rwa [h1] at h2

omit [Finite Dm] in
/-- **The preembedding maps an R-link path of the kernel to an R-link path.** -/
theorem isChain_map_embed (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) :
    ∀ (p : List Dc) (x : Dc), List.IsChain Gc.Rlink (x :: p) →
      (∀ z ∈ x :: p, Gc.Kernel rc z) → List.IsChain Gm.Rlink ((x :: p).map h) := by
  intro p
  induction p with
  | nil => intro x _ _; exact List.isChain_singleton _
  | cons w p ih =>
    intro x hc hk
    have hcc := List.isChain_cons_cons.mp hc
    refine List.isChain_cons_cons.mpr ⟨?_, ih w hcc.2
      (fun z hz => hk z (List.mem_cons_of_mem _ hz))⟩
    exact rlink_map_embed hemb hplainm hcubm hpre (hk x List.mem_cons_self)
      (hk w (List.mem_cons_of_mem _ List.mem_cons_self)) hcc.1

/-- `PreHomRing Gc Gm rc h x p`: the darts `x :: p` form an R-link path inside
the kernel of `rc` whose image under `h` is a face-simple R-cycle.  This is the
reference's `pre_hom_ring`. -/
structure PreHomRing (Gc : Hypermap Dc) (Gm : Hypermap Dm) (rc : List Dc) (h : Dc → Dm)
    (x : Dc) (p : List Dc) : Prop where
  /-- The darts form an R-link path. -/
  chain : List.IsChain Gc.Rlink (x :: p)
  /-- The darts lie in the kernel of the perimeter. -/
  kernel : ∀ z ∈ x :: p, Gc.Kernel rc z
  /-- The image is a face-simple R-cycle. -/
  scycle : Gm.Scycle Gm.Rlink ((x :: p).map h)

omit [Finite Dm] in
/-- **Introduction rule for `Hypermap.PreHomRing`.**  This is the reference's
`intro_pre_hom_ring`. -/
theorem intro_preHomRing (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} {p : List Dc}
    (hchain : List.IsChain Gc.Rlink (x :: p))
    (hlast : Gm.Rlink (h (p.getLastD x)) (h x))
    (hker : ∀ z ∈ x :: p, Gc.Kernel rc z)
    (hsimple : Gm.Simple ((x :: p).map h)) :
    PreHomRing Gc Gm rc h x p := by
  classical
  refine ⟨hchain, hker, ?_, hsimple⟩
  have hmapchain : List.IsChain Gm.Rlink ((x :: p).map h) :=
    isChain_map_embed hemb hplainm hcubm hpre p x hchain hker
  have hmap : (x :: p).map h = h x :: p.map h := by simp
  rw [hmap] at hmapchain ⊢
  refine isCyclicChain_cons.mpr ⟨hmapchain, ?_⟩
  rw [getLast_cons_eq_getLastD, List.getLastD_map]
  exact hlast

end HomRing

/-! ### Trivial homomorphic rings

A homomorphic ring whose image bounds no face at all closes up: its last dart is
R-linked to its first.  This is the reference's `trivial_hom_ring`, proved by
induction on the length of the ring, cutting the image ring along the chord
`edge (node (h y))` for the last dart `y`. -/

section TrivialHomRing

/-- Reading an arc of a duplicate-free ring off one of its rotations. -/
private theorem arc_eq_of_rotate {α : Type*} [DecidableEq α] {r : List α} (hnd : r.Nodup)
    {m : ℕ} {u v : α} {s t : List α} (hrot : r.rotate m = (u :: s) ++ (v :: t)) :
    arc r u v = u :: s := by
  have hnd2 : ((u :: s) ++ (v :: t)).Nodup := by
    rw [← hrot]; exact List.nodup_rotate.mpr hnd
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd2
  have h1 : rotTo r u = (u :: s) ++ (v :: t) := by
    refine rotTo_eq_of_rotate hnd (m := m) ?_
    rw [hrot]; rfl
  exact arc_eq_of_rotTo h1 (fun hc => hdisj v hc v List.mem_cons_self rfl)

omit [Finite Dc] in
/-- A ring cut out of a chord ring of a face-free ring is itself face-free. -/
private theorem diskF_nil_of_chordRing (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) {r : List Dm}
    (hscyc : Gm.Scycle Gm.Rlink r) (hproper : Gm.ProperRing r) {c : Dm}
    (hdE : Gm.DiskE r c) (hb : Gm.Fband r c) (hbe : Gm.Fband r (Gm.edge c))
    (hF0 : ∀ u : Dm, ¬ Gm.DiskF r u) {s : List Dm} {m : ℕ}
    (hs : s.rotate m = Gm.chordRing r c) : ∀ u : Dm, ¬ Gm.DiskF s u := by
  classical
  intro u hu
  rw [← diskF_rotate (n := m), hs] at hu
  exact hF0 u
    ((diskF_chordRing hplanm hplainm hbridgem hconnm hscyc hproper hdE hb hbe).mp hu).1

/-- **A homomorphic ring whose image bounds no face closes up.**  This is the
induction behind the reference's `trivial_hom_ring`. -/
private theorem trivial_hom_ring_aux (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (n : ℕ) :
    ∀ (x : Dc) (p : List Dc), p.length ≤ n → PreHomRing Gc Gm rc h x p →
      (∀ u : Dm, ¬ Gm.DiskF ((x :: p).map h) u) → Gc.Rlink (p.getLastD x) x := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
  have hempty : ∀ x' : Dc, ¬ PreHomRing Gc Gm rc h x' [] := by
    intro x' hr
    have h1 : Gm.Rlink (h x') (h x') := by simpa using hr.scycle.isCyclicChain
    exact hbridgem (h x') h1.symm
  have hfem : ∀ u : Dm, Gm.face (Gm.edge u) = Gm.node (Gm.node u) := by
    intro u
    have hk := Gm.nodeK (Gm.node (Gm.node u))
    rwa [hcubm.node_node_node u] at hk
  have hcfen : ∀ u : Dm, Gm.CFace (Gm.edge (Gm.node u)) u := by
    intro u
    have h0 := Gm.cface_face (Gm.edge (Gm.node u))
    rwa [Gm.nodeK u] at h0
  induction n with
  | zero =>
    intro x p hlen hring _
    rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
    subst hlen
    exact absurd hring (hempty x)
  | succ n ihn =>
  intro x p hlen hring hF0
  by_cases hpnil : p = []
  · subst hpnil
    exact absurd hring (hempty x)
  have ih : ∀ (x' : Dc) (p' : List Dc), p'.length < p.length →
      PreHomRing Gc Gm rc h x' p' →
      (∀ u : Dm, ¬ Gm.DiskF ((x' :: p').map h) u) → Gc.Rlink (p'.getLastD x') x' := by
    intro x' p' hlt
    exact ihn x' p' (by omega)
  have hchain := hring.chain
  have hker := hring.kernel
  have hURh := hring.scycle
  have hsimpleh : Gm.Simple ((x :: p).map h) := hURh.simple
  have hnoduph : ((x :: p).map h).Nodup := hsimpleh.nodup
  have hinj : ∀ a ∈ (x :: p), ∀ b ∈ (x :: p), h a = h b → a = b :=
    List.inj_on_of_nodup_map hnoduph
  have hnodup : (x :: p).Nodup := List.Nodup.of_map h hnoduph
  have hnodup_p : p.Nodup := (List.nodup_cons.mp hnodup).2
  have hhx_mem : h x ∈ (x :: p).map h := List.mem_map.mpr ⟨x, List.mem_cons_self, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ t : Dc, t = p.getLastD x := ⟨_, rfl⟩
  have hy_p : y ∈ p := by rw [hydef]; exact getLastD_mem p x hpnil
  have hy_xp : y ∈ (x :: p) := List.mem_cons_of_mem _ hy_p
  have hky : Gc.Kernel rc y := hker y hy_xp
  have hhy_mem : h y ∈ (x :: p).map h := List.mem_map.mpr ⟨y, hy_xp, rfl⟩
  have hmapcons : (x :: p).map h = h x :: p.map h := by simp
  have hcych : IsCyclicChain Gm.Rlink (h x :: p.map h) := by
    rw [← hmapcons]; exact hURh.isCyclicChain
  have hhyRhx : Gm.Rlink (h y) (h x) := by
    have h1 := (isCyclicChain_cons.mp hcych).2
    rwa [getLast_cons_eq_getLastD, List.getLastD_map, ← hydef] at h1
  have hband_nhy : Gm.Fband ((x :: p).map h) (Gm.node (h y)) := by
    by_contra hnb
    exact hF0 (Gm.node (h y)) ⟨diskN_node (diskN_of_mem hhy_mem), hnb⟩
  obtain ⟨w, hw_mem, hwcf⟩ := id hband_nhy
  obtain ⟨z, hz_xp, hzw⟩ := List.mem_map.mp hw_mem
  subst hzw
  have hzF : Gm.CFace (h z) (Gm.node (h y)) := hwcf.symm
  have hkz : Gc.Kernel rc z := hker z hz_xp
  have hhz_mem : h z ∈ (x :: p).map h := List.mem_map.mpr ⟨z, hz_xp, rfl⟩
  -- the chord dart is not the head of the ring
  have hz_ne_x : z ≠ x := by
    rintro rfl
    have h1 : Gm.CFace (Gm.edge (h y)) (Gm.node (h y)) := hhyRhx.trans hzF
    have h3 : Gm.CFace (Gm.node (Gm.node (h y))) (Gm.node (h y)) := by
      rw [← hfem (h y)]
      exact ((Gm.cface_face (Gm.edge (h y))).symm).trans h1
    exact hbridgem _ (h3.trans (hcfen (Gm.node (h y))).symm)
  -- split the ring at the chord dart and at its last dart
  have hz_p : z ∈ p := (List.mem_cons.mp hz_xp).resolve_left hz_ne_x
  obtain ⟨A, B0, hp0⟩ := List.append_of_mem hz_p
  have hB0_ne : B0 ≠ [] := by
    rintro rfl
    have hyz : y = z := by rw [hydef, hp0]; exact List.getLastD_concat
    rw [hyz] at hzF
    exact hbridgem _ (hzF.symm.trans (hcfen (h z)).symm)
  obtain ⟨B, y', hB0⟩ : ∃ B y', B0 = B ++ [y'] :=
    ⟨B0.dropLast, B0.getLast hB0_ne, (List.dropLast_append_getLast hB0_ne).symm⟩
  have hy'y : y' = y := by
    have h1 : A ++ z :: (B ++ [y']) = (A ++ z :: B) ++ [y'] := by simp
    rw [hydef, hp0, hB0, h1, List.getLastD_concat]
  rw [hy'y] at hB0
  have hp : p = A ++ z :: (B ++ [y]) := by rw [hp0, hB0]
  have hnd_sub : (z :: (B ++ [y])).Nodup := by
    have h1 := hnodup_p
    rw [hp] at h1
    exact (List.nodup_append.mp h1).2.1
  have hchain_all : List.IsChain Gc.Rlink (x :: (A ++ z :: (B ++ [y]))) := by
    rw [← hp]; exact hchain
  have hRzy_chain : List.IsChain Gc.Rlink (z :: (B ++ [y])) :=
    hchain_all.suffix ⟨x :: A, by simp⟩
  have hRxz_chain : List.IsChain Gc.Rlink (x :: (A ++ [z])) :=
    hchain_all.prefix ⟨B ++ [y], by simp⟩
  have hA_xp : ∀ v ∈ A, v ∈ (x :: p) := by
    intro v hv; rw [hp]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
  have hB_xp : ∀ v ∈ B, v ∈ (x :: p) := by
    intro v hv
    rw [hp]
    exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hv)))
  -- the first chord
  obtain ⟨eny, heny⟩ : ∃ t : Dc, t = Gc.edge (Gc.node y) := ⟨_, rfl⟩
  have hface_eny : Gc.face eny = y := by rw [heny]; exact Gc.nodeK y
  have hedge_eny : Gc.edge eny = Gc.node y := by rw [heny]; exact hplainc.edge_edge _
  have hker_eny : Gc.Kernel rc eny := by rw [← kernel_face, hface_eny]; exact hky
  have hcf_eny_y : Gc.CFace eny y := by
    have h0 := Gc.cface_face eny
    rwa [hface_eny] at h0
  have h_eny : h eny = Gm.edge (Gm.node (h y)) := by
    have h1 := hpre.face eny hker_eny
    rw [hface_eny] at h1
    refine Gm.face.injective ?_
    rw [← h1, Gm.nodeK]
  have hedge_heny : Gm.edge (h eny) = Gm.node (h y) := by rw [h_eny, hplainm.edge_edge]
  have hcf_heny_hy : Gm.CFace (h eny) (h y) := by rw [h_eny]; exact hcfen (h y)
  -- the image ring and its arcs
  have hproper_r : Gm.ProperRing ((x :: p).map h) := by
    refine Gm.properRing_of_two_lt_length ?_
    rw [List.length_map, hp]
    simp only [List.length_cons, List.length_append]
    omega
  have hr_split : (x :: p).map h = (h x :: A.map h) ++ ((h z :: B.map h) ++ [h y]) := by
    rw [hp]; simp
  have harc_zy : arc ((x :: p).map h) (h z) (h y) = h z :: B.map h := by
    refine arc_eq_of_rotate hnoduph (m := (h x :: A.map h).length)
      (t := h x :: A.map h) ?_
    rw [hr_split, List.rotate_append_length_eq]
    simp
  have harc_xz : arc ((x :: p).map h) (h x) (h z) = h x :: A.map h := by
    refine arc_eq_of_rotate hnoduph (m := 0) (t := B.map h ++ [h y]) ?_
    rw [List.rotate_zero, hr_split]
    simp
  have hfproj_heny : Gm.fproj ((x :: p).map h) (h eny) = h y :=
    hsimpleh.fproj_eq hhy_mem hcf_heny_hy
  have hfproj_nhy : Gm.fproj ((x :: p).map h) (Gm.node (h y)) = h z :=
    hsimpleh.fproj_eq hhz_mem hzF.symm
  -- the first chord closes the right arc
  have henyRz : Gc.Rlink eny z := by
    by_cases hzn : h z = Gm.node (h y)
    · have hBnil : B = [] := by
        rcases B with _ | ⟨b0, B'⟩
        · rfl
        · exfalso
          have hb0_xp : b0 ∈ (x :: p) := hB_xp b0 List.mem_cons_self
          have hb0_hmem : h b0 ∈ (x :: p).map h := List.mem_map.mpr ⟨b0, hb0_xp, rfl⟩
          have hRzb : Gc.Rlink z b0 := (List.isChain_cons_cons.mp hRzy_chain).1
          have hRhzb : Gm.Rlink (h z) (h b0) :=
            rlink_map_embed hemb hplainm hcubm hpre hkz (hker b0 hb0_xp) hRzb
          rw [hzn] at hRhzb
          have hcf : Gm.CFace (h y) (h b0) := (hcfen (h y)).symm.trans hRhzb
          have heq : h y = h b0 := hsimpleh.eq_of_cface hhy_mem hb0_hmem hcf
          have hyb : y = b0 := hinj y hy_xp b0 hb0_xp heq
          have hnd2 : (b0 :: (B' ++ [y])).Nodup := (List.nodup_cons.mp hnd_sub).2
          exact (List.nodup_cons.mp hnd2).1
            (by rw [← hyb]; exact List.mem_append_right _ List.mem_cons_self)
      subst hBnil
      have hRzy : Gc.Rlink z y := (List.isChain_cons_cons.mp hRzy_chain).1
      have hker_ez : Gc.Kernel rc (Gc.edge z) := (Kernel.congr hRzy).mpr hky
      have hcf_ez_eny : Gc.CFace (Gc.edge z) eny := hRzy.trans hcf_eny_y.symm
      have h_ez : h (Gc.edge z) = h eny := by
        rw [embed_functor hemb hplainm hcubm hpre hkz hker_ez, hzn, h_eny]
      have hez : Gc.edge z = eny := cface_inj_embed hpre hker_ez hcf_ez_eny h_ez
      have hzn2 : z = Gc.node y := by
        have h1 : Gc.edge (Gc.edge z) = Gc.edge eny := by rw [hez]
        rwa [hplainc.edge_edge, hedge_eny] at h1
      have hfin : Gc.CFace (Gc.edge eny) z := by
        rw [hedge_eny, ← hzn2]
      exact hfin
    · have hnhy_notin : Gm.node (h y) ∉ (x :: p).map h := fun hmem =>
        hzn (hsimpleh.eq_of_cface hhz_mem hmem hzF)
      have hchain_new : List.IsChain Gc.Rlink (z :: (B ++ [eny])) := by
        have h1 : z :: (B ++ [y]) = (z :: B) ++ [y] := by simp
        rw [h1] at hRzy_chain
        obtain ⟨hc1, -, hc3⟩ := List.isChain_append.mp hRzy_chain
        have h2 : z :: (B ++ [eny]) = (z :: B) ++ [eny] := by simp
        rw [h2]
        refine hc1.append (List.isChain_singleton _) ?_
        intro u hu v hv
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        subst hv
        exact (hc3 u hu y (by simp)).trans hcf_eny_y.symm
      have hker_new : ∀ v ∈ z :: (B ++ [eny]), Gc.Kernel rc v := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hkz
        · rcases List.mem_append.mp hv with hv | hv
          · exact hker v (hB_xp v hv)
          · simp only [List.mem_singleton] at hv
            rw [hv]; exact hker_eny
      have hlast_new : Gm.Rlink (h ((B ++ [eny]).getLastD z)) (h z) := by
        rw [List.getLastD_concat]
        change Gm.CFace (Gm.edge (h eny)) (h z)
        rw [hedge_heny]
        exact hzF.symm
      have hsimple_new : Gm.Simple ((z :: (B ++ [eny])).map h) := by
        have hseg : Gm.Simple ((h z :: B.map h) ++ [h y]) := by
          have h1 := hsimpleh
          rw [hr_split] at h1
          exact (simple_append.mp h1).2.1
        have h2 : (z :: (B ++ [eny])).map h = (h z :: B.map h) ++ [h eny] := by simp
        rw [h2, simple_concat]
        refine ⟨fun hb => (simple_concat.mp hseg).1 ((Fband.congr hcf_heny_hy).mp hb),
          (simple_concat.mp hseg).2⟩
      have hring_new : PreHomRing Gc Gm rc h z (B ++ [eny]) :=
        intro_preHomRing hemb hplainm hcubm hpre hchain_new hlast_new hker_new hsimple_new
      have hchord_eq : Gm.chordRing ((x :: p).map h) (h eny) = h eny :: (h z :: B.map h) := by
        simp only [chordRing, hedge_heny, hfproj_nhy, hfproj_heny, harc_zy]
      have hF0_new : ∀ u : Dm, ¬ Gm.DiskF ((z :: (B ++ [eny])).map h) u := by
        refine diskF_nil_of_chordRing hplanm hplainm hbridgem hconnm hURh hproper_r
          (c := h eny) ?_ ?_ ?_ hF0 (m := (h z :: B.map h).length) ?_
        · rw [h_eny]
          exact (diskE_edge_iff hplanm hURh).mpr
            ⟨diskN_node (diskN_of_mem hhy_mem), hnhy_notin⟩
        · exact ⟨h y, hhy_mem, hcf_heny_hy⟩
        · rw [hedge_heny]; exact hband_nhy
        · have h2 : (z :: (B ++ [eny])).map h = (h z :: B.map h) ++ [h eny] := by simp
          rw [h2, List.rotate_append_length_eq, hchord_eq]
          simp
      have hlt : (B ++ [eny]).length < p.length := by
        rw [hp]
        simp only [List.length_cons, List.length_append]
        omega
      have hres := ih z (B ++ [eny]) hlt hring_new hF0_new
      rwa [List.getLastD_concat] at hres
  -- the node of the last dart is in the kernel and commutes with the embedding
  have hk_ny : Gc.Kernel rc (Gc.node y) := by
    have h1 : Gc.Kernel rc (Gc.edge eny) := (Kernel.congr henyRz).mpr hkz
    rwa [hedge_eny] at h1
  have h_ny : h (Gc.node y) = Gm.node (h y) := by
    have h1 : h (Gc.edge eny) = Gm.edge (h eny) :=
      embed_functor hemb hplainm hcubm hpre hker_eny (by rw [hedge_eny]; exact hk_ny)
    rwa [hedge_eny, h_eny, hplainm.edge_edge] at h1
  have hcf_ny_z : Gc.CFace (Gc.node y) z := by
    have h1 : Gc.CFace (Gc.edge eny) z := henyRz
    rwa [hedge_eny] at h1
  -- the second chord
  obtain ⟨enny, hennydef⟩ : ∃ t : Dc, t = Gc.edge (Gc.node (Gc.node y)) := ⟨_, rfl⟩
  have hface_enny : Gc.face enny = Gc.node y := by
    rw [hennydef]; exact Gc.nodeK (Gc.node y)
  have hedge_enny : Gc.edge enny = Gc.node (Gc.node y) := by
    rw [hennydef]; exact hplainc.edge_edge _
  have hker_enny : Gc.Kernel rc enny := by rw [← kernel_face, hface_enny]; exact hk_ny
  have hcf_enny_ny : Gc.CFace enny (Gc.node y) := by
    have h0 := Gc.cface_face enny
    rwa [hface_enny] at h0
  have hcf_enny_z : Gc.CFace enny z := hcf_enny_ny.trans hcf_ny_z
  have h_enny : h enny = Gm.edge (Gm.node (Gm.node (h y))) := by
    have h1 := hpre.face enny hker_enny
    rw [hface_enny, h_ny] at h1
    refine Gm.face.injective ?_
    rw [← h1, Gm.nodeK]
  have hedge_henny : Gm.edge (h enny) = Gm.node (Gm.node (h y)) := by
    rw [h_enny, hplainm.edge_edge]
  have hcf_henny_nhy : Gm.CFace (h enny) (Gm.node (h y)) := by
    rw [h_enny]; exact hcfen (Gm.node (h y))
  have hcf_henny_hz : Gm.CFace (h enny) (h z) := hcf_henny_nhy.trans hzF.symm
  have hcf_nnhy_hx : Gm.CFace (Gm.node (Gm.node (h y))) (h x) := by
    rw [← hfem (h y)]
    exact ((Gm.cface_face (Gm.edge (h y))).symm).trans hhyRhx
  have hfproj_henny : Gm.fproj ((x :: p).map h) (h enny) = h z :=
    hsimpleh.fproj_eq hhz_mem hcf_henny_hz
  have hfproj_nnhy : Gm.fproj ((x :: p).map h) (Gm.node (Gm.node (h y))) = h x :=
    hsimpleh.fproj_eq hhx_mem hcf_nnhy_hx
  -- the second chord closes the left arc
  have hennyRx : Gc.Rlink enny x := by
    by_cases hxn : h x = Gm.node (Gm.node (h y))
    · have hAnil : A = [] := by
        rcases A with _ | ⟨a0, A'⟩
        · rfl
        · exfalso
          have ha0_xp : a0 ∈ (x :: p) := hA_xp a0 List.mem_cons_self
          have ha0_hmem : h a0 ∈ (x :: p).map h := List.mem_map.mpr ⟨a0, ha0_xp, rfl⟩
          have hRxa : Gc.Rlink x a0 := (List.isChain_cons_cons.mp hRxz_chain).1
          have hRhxa : Gm.Rlink (h x) (h a0) :=
            rlink_map_embed hemb hplainm hcubm hpre (hker x List.mem_cons_self)
              (hker a0 ha0_xp) hRxa
          rw [hxn] at hRhxa
          have hcf : Gm.CFace (Gm.node (h y)) (h a0) :=
            (hcfen (Gm.node (h y))).symm.trans hRhxa
          have heq : h z = h a0 := hsimpleh.eq_of_cface hhz_mem ha0_hmem (hzF.trans hcf)
          have hza : z = a0 := hinj z hz_xp a0 ha0_xp heq
          have hnd1 : ((a0 :: A') ++ z :: (B ++ [y])).Nodup := by rw [← hp]; exact hnodup_p
          obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd1
          exact hdisj a0 List.mem_cons_self z List.mem_cons_self hza.symm
      subst hAnil
      have hRxz : Gc.Rlink x z := (List.isChain_cons_cons.mp hRxz_chain).1
      have hker_ex : Gc.Kernel rc (Gc.edge x) := (Kernel.congr hRxz).mpr hkz
      have hcf_ex_enny : Gc.CFace (Gc.edge x) enny := hRxz.trans hcf_enny_z.symm
      have h_ex : h (Gc.edge x) = h enny := by
        rw [embed_functor hemb hplainm hcubm hpre (hker x List.mem_cons_self) hker_ex,
          hxn, h_enny]
      have hex : Gc.edge x = enny := cface_inj_embed hpre hker_ex hcf_ex_enny h_ex
      have hxnn : x = Gc.node (Gc.node y) := by
        have h1 : Gc.edge (Gc.edge x) = Gc.edge enny := by rw [hex]
        rwa [hplainc.edge_edge, hedge_enny] at h1
      have hfin : Gc.CFace (Gc.edge enny) x := by
        rw [hedge_enny, ← hxnn]
      exact hfin
    · have hnnhy_notin : Gm.node (Gm.node (h y)) ∉ (x :: p).map h := fun hmem =>
        hxn (hsimpleh.eq_of_cface hhx_mem hmem hcf_nnhy_hx.symm)
      have hchain_new : List.IsChain Gc.Rlink (x :: (A ++ [enny])) := by
        have h1 : x :: (A ++ [z]) = (x :: A) ++ [z] := by simp
        rw [h1] at hRxz_chain
        obtain ⟨hc1, -, hc3⟩ := List.isChain_append.mp hRxz_chain
        have h2 : x :: (A ++ [enny]) = (x :: A) ++ [enny] := by simp
        rw [h2]
        refine hc1.append (List.isChain_singleton _) ?_
        intro u hu v hv
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
        subst hv
        exact (hc3 u hu z (by simp)).trans hcf_enny_z.symm
      have hker_new : ∀ v ∈ x :: (A ++ [enny]), Gc.Kernel rc v := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hker v List.mem_cons_self
        · rcases List.mem_append.mp hv with hv | hv
          · exact hker v (hA_xp v hv)
          · simp only [List.mem_singleton] at hv
            rw [hv]; exact hker_enny
      have hlast_new : Gm.Rlink (h ((A ++ [enny]).getLastD x)) (h x) := by
        rw [List.getLastD_concat]
        change Gm.CFace (Gm.edge (h enny)) (h x)
        rw [hedge_henny]
        exact hcf_nnhy_hx
      have hsimple_new : Gm.Simple ((x :: (A ++ [enny])).map h) := by
        have hseg : Gm.Simple ((h x :: A.map h) ++ [h z]) := by
          have h1 : (x :: p).map h
              = ((h x :: A.map h) ++ [h z]) ++ (B.map h ++ [h y]) := by
            rw [hp]; simp
          have h2 := hsimpleh
          rw [h1] at h2
          exact (simple_append.mp h2).1
        have h2 : (x :: (A ++ [enny])).map h = (h x :: A.map h) ++ [h enny] := by simp
        rw [h2, simple_concat]
        refine ⟨fun hb => (simple_concat.mp hseg).1 ((Fband.congr hcf_henny_hz).mp hb),
          (simple_concat.mp hseg).2⟩
      have hring_new : PreHomRing Gc Gm rc h x (A ++ [enny]) :=
        intro_preHomRing hemb hplainm hcubm hpre hchain_new hlast_new hker_new hsimple_new
      have hchord_eq : Gm.chordRing ((x :: p).map h) (h enny)
          = h enny :: (h x :: A.map h) := by
        simp only [chordRing, hedge_henny, hfproj_nnhy, hfproj_henny, harc_xz]
      have hF0_new : ∀ u : Dm, ¬ Gm.DiskF ((x :: (A ++ [enny])).map h) u := by
        refine diskF_nil_of_chordRing hplanm hplainm hbridgem hconnm hURh hproper_r
          (c := h enny) ?_ ?_ ?_ hF0 (m := (h x :: A.map h).length) ?_
        · rw [h_enny]
          exact (diskE_edge_iff hplanm hURh).mpr
            ⟨diskN_node (diskN_node (diskN_of_mem hhy_mem)), hnnhy_notin⟩
        · exact ⟨h z, hhz_mem, hcf_henny_hz⟩
        · rw [hedge_henny]; exact ⟨h x, hhx_mem, hcf_nnhy_hx⟩
        · have h2 : (x :: (A ++ [enny])).map h = (h x :: A.map h) ++ [h enny] := by simp
          rw [h2, List.rotate_append_length_eq, hchord_eq]
          simp
      have hlt : (A ++ [enny]).length < p.length := by
        rw [hp]
        simp only [List.length_cons, List.length_append]
        omega
      have hres := ih x (A ++ [enny]) hlt hring_new hF0_new
      rwa [List.getLastD_concat] at hres
  -- the ring closes up
  have hybc : y ∉ rc := not_mem_of_kernel hky
  have hn3y : Gc.node (Gc.node (Gc.node y)) = y := hqc.node_node_node hybc
  have hfey : Gc.face (Gc.edge y) = Gc.node (Gc.node y) := by
    have hk := Gc.nodeK (Gc.node (Gc.node y))
    rwa [hn3y] at hk
  have hfin : Gc.CFace (Gc.edge y) x := by
    have h1 : Gc.CFace (Gc.edge enny) x := hennyRx
    rw [hedge_enny, ← hfey] at h1
    exact (Gc.cface_face (Gc.edge y)).trans h1
  rw [← hydef]
  exact hfin

/-- **A homomorphic ring whose image bounds no face closes up.**  This is the
reference's `trivial_hom_ring`. -/
theorem trivial_hom_ring (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc}
    {p : List Dc} (hring : PreHomRing Gc Gm rc h x p)
    (hF0 : ∀ u : Dm, ¬ Gm.DiskF ((x :: p).map h) u) : Gc.Rlink (p.getLastD x) x :=
  trivial_hom_ring_aux hemb hplanm hplainm hbridgem hconnm hcubm hpre p.length x p le_rfl
    hring hF0

end TrivialHomRing

/-! ### Fullness of the embedding

The preembedding reflects E-links: if `edge (h x1) = h x2` for two kernel darts,
then already `edge x1 = x2`.  This is the reference's `embed_full`, proved by
ruling out, in four successive reductions, a homomorphic ring that fails to
close up. -/

section EmbedFull

/-- **The innermost step of `embed_full`**: a five-dart homomorphic ring that
does not close up and whose image bounds at most one face bounds none at all.
The face it would bound is surrounded by the image ring, which therefore runs
around it by `face ∘ face ∘ edge`; the nodes of the ring darts then give five
distinct darts pointing into the kernel out of one face, which
`Hypermap.adj_kernel_max` forbids. -/
private theorem embed_full_noface (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} {p : List Dc}
    (hring : PreHomRing Gc Gm rc h x p) (hLp : ¬ Gc.Rlink (p.getLastD x) x)
    (hlen5 : (x :: p).length = 5)
    (hF1 : Gm.faceCard (Gm.DiskF ((x :: p).map h)) ≤ 1) :
    ∀ u : Dm, ¬ Gm.DiskF ((x :: p).map h) u := by
  classical
  intro u hu
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
  have hchain := hring.chain
  have hker := hring.kernel
  have hURh := hring.scycle
  have hsimpleh : Gm.Simple ((x :: p).map h) := hURh.simple
  have hnoduph : ((x :: p).map h).Nodup := hsimpleh.nodup
  have hnodup : (x :: p).Nodup := List.Nodup.of_map h hnoduph
  have hhmem : ∀ v ∈ (x :: p), h v ∈ ((x :: p).map h) :=
    fun v hv => List.mem_map.mpr ⟨v, hv, rfl⟩
  -- the image ring bounds exactly one face
  have hDdF : ∀ v : Dm, Gm.DiskF ((x :: p).map h) v ↔ Gm.CFace u v := by
    intro v
    refine ⟨fun hv => ?_, fun hcf => (diskF_congr hcf).mp hu⟩
    by_contra hcf
    have h1 := one_lt_faceCard.mpr ⟨u, v, hu, hv, hcf⟩
    omega
  -- the spoke ring of that face
  have hURu : Gm.Scycle Gm.Rlink (Gm.spokeRing u) :=
    scycle_spokeRing hplanm hplainm hbridgem hcubm hBm u
  have hsubF : ∀ v : Dm, Gm.Fband (Gm.spokeRing u) v → Gm.Fband ((x :: p).map h) v := by
    rintro v ⟨w, hw, hvw⟩
    refine (Fband.congr hvw).mpr ?_
    have hufnw : Gm.CFace u (Gm.node w) := mem_spokeRing.mp hw
    have hdNw : Gm.DiskN ((x :: p).map h) w := diskN_node_iff.mp ((hDdF _).mpr hufnw).1
    by_contra hb
    have h1 : Gm.CFace w (Gm.node w) := ((hDdF w).mp ⟨hdNw, hb⟩).symm.trans hufnw
    have h2 : Gm.CFace (Gm.edge (Gm.node w)) w := by
      have h3 := Gm.cface_face (Gm.edge (Gm.node w))
      rwa [Gm.nodeK w] at h3
    exact hbridgem (Gm.node w) (h1.symm.trans h2.symm)
  -- the two rings meet the same faces
  have hcard_hxp :
      (((x :: p).map h).map (Quotient.mk (SameCycle.setoid Gm.face))).toFinset.card = 5 := by
    rw [hsimpleh.card_faces, List.length_map, hlen5]
  have hcard_ru : ((Gm.spokeRing u).map
      (Quotient.mk (SameCycle.setoid Gm.face))).toFinset.card = Gm.arity u := by
    rw [hURu.simple.card_faces, length_spokeRing]
  have hsub : ((Gm.spokeRing u).map (Quotient.mk (SameCycle.setoid Gm.face))).toFinset ⊆
      (((x :: p).map h).map (Quotient.mk (SameCycle.setoid Gm.face))).toFinset := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact List.mem_toFinset.mpr (mem_map_quotient_iff_fband.mpr (hsubF v (fband_of_mem hv)))
  have harity5 : Gm.arity u = 5 := by
    have hle : Gm.arity u ≤ 5 := by
      rw [← hcard_ru, ← hcard_hxp]
      exact Finset.card_le_card hsub
    have h4 := hpentm u
    omega
  have hband_eq : ∀ v : Dm, Gm.Fband ((x :: p).map h) v ↔ Gm.Fband (Gm.spokeRing u) v := by
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard_hxp, hcard_ru, harity5])
    intro v
    rw [← mem_toFinset_map_quotient_iff, ← mem_toFinset_map_quotient_iff, heq]
  -- the image ring lies on the spoke ring
  have hproper : Gm.ProperRing ((x :: p).map h) := by
    refine Gm.properRing_of_two_lt_length ?_
    rw [List.length_map, hlen5]
    omega
  have hsub_ru : ∀ v ∈ ((x :: p).map h), v ∈ Gm.spokeRing u := by
    intro v hv
    have hadj1 : Gm.Adj u v := fband_spokeRing.mp ((hband_eq v).mp (fband_of_mem hv))
    have hadj2 : Gm.Adj u (Gm.edge v) := by
      refine fband_spokeRing.mp ((hband_eq _).mp ⟨((x :: p).map h).next v hv,
        List.next_mem _ _ _, ?_⟩)
      exact rel_next hURh.isCyclicChain hnoduph hv
    rcases adj11_edge hplanm hplainm hbridgem hcubm hBm hadj1 hadj2 with hres | hres
    · exact hres
    · exact absurd (diskN_node_iff.mp ((hDdF _).mpr (mem_spokeRing.mp hres)).1)
        (diskN_edge_ring hplanm hplainm hURh hproper hv)
  -- the image ring runs around the face by `face ∘ face ∘ edge`
  have hnext_eq : ∀ (v : Dm) (hv : v ∈ ((x :: p).map h)),
      ((x :: p).map h).next v hv = Gm.face (Gm.face (Gm.edge v)) := by
    intro v hv
    have hv_ru : v ∈ Gm.spokeRing u := hsub_ru v hv
    have hnr : (Gm.spokeRing u).next v hv_ru = Gm.face (Gm.spoke v) :=
      next_spokeRing hplainm hcubm hv_ru
    have h1 : Gm.Rlink v (((x :: p).map h).next v hv) :=
      rel_next hURh.isCyclicChain hnoduph hv
    have h2 : Gm.Rlink v ((Gm.spokeRing u).next v hv_ru) :=
      rel_next hURu.isCyclicChain (Gm.nodup_spokeRing u) hv_ru
    have h3 : ((x :: p).map h).next v hv = (Gm.spokeRing u).next v hv_ru :=
      hURu.simple.eq_of_cface (hsub_ru _ (List.next_mem _ _ _)) (List.next_mem _ _ _)
        (h1.symm.trans h2)
    have h4 : Gm.spoke v = Gm.face (Gm.edge v) := rfl
    rw [h3, hnr, h4]
  have hFFE : ∀ a b : Dc, a ∈ (x :: p) → b ∈ (x :: p) → Gm.Rlink (h a) (h b) →
      h b = Gm.face (Gm.face (Gm.edge (h a))) := by
    intro a b ha hb hab
    have hahm : h a ∈ ((x :: p).map h) := hhmem a ha
    have h1 : Gm.Rlink (h a) (((x :: p).map h).next (h a) hahm) :=
      rel_next hURh.isCyclicChain hnoduph hahm
    have h2 : ((x :: p).map h).next (h a) hahm = h b :=
      hsimpleh.eq_of_cface (List.next_mem _ _ _) (hhmem b hb) (h1.symm.trans hab)
    rw [← h2, hnext_eq]
  -- consecutive ring darts have their nodes in one face
  have hnn : ∀ a b : Dc, a ∈ (x :: p) → b ∈ (x :: p) → Gc.Rlink a b →
      Gc.CFace (Gc.node a) (Gc.node b) := by
    intro a b ha hb hab
    have hka : Gc.Kernel rc a := hker a ha
    have hkb : Gc.Kernel rc b := hker b hb
    have hkea : Gc.Kernel rc (Gc.edge a) := (Kernel.congr hab).mpr hkb
    have hkfea : Gc.Kernel rc (Gc.face (Gc.edge a)) := kernel_face.mpr hkea
    have he1 : h (Gc.edge a) = Gm.edge (h a) :=
      embed_functor hemb hplainm hcubm hpre hka hkea
    have he2 : h (Gc.face (Gc.edge a)) = Gm.face (Gm.edge (h a)) := by
      rw [hpre.face _ hkea, he1]
    have he3 : h (Gc.face (Gc.face (Gc.edge a))) = Gm.face (Gm.face (Gm.edge (h a))) := by
      rw [hpre.face _ hkfea, he2]
    have hbeq : h b = h (Gc.face (Gc.face (Gc.edge a))) := by
      rw [he3]
      exact hFFE a b ha hb (rlink_map_embed hemb hplainm hcubm hpre hka hkb hab)
    have hcfb : Gc.CFace b (Gc.face (Gc.face (Gc.edge a))) :=
      hab.symm.trans ((Gc.cface_face (Gc.edge a)).trans
        (Gc.cface_face (Gc.face (Gc.edge a))))
    have hb2 : b = Gc.face (Gc.face (Gc.edge a)) := cface_inj_embed hpre hkb hcfb hbeq
    have habc : a ∉ rc := not_mem_of_kernel hka
    have hn3a : Gc.node (Gc.node (Gc.node a)) = a := hqc.node_node_node habc
    have hfea : Gc.face (Gc.edge a) = Gc.node (Gc.node a) := by
      have hk := Gc.nodeK (Gc.node (Gc.node a))
      rwa [hn3a] at hk
    have hnb : Gc.node b = Gc.edge (Gc.node (Gc.node a)) := by
      rw [hb2, hfea]
      have hk := Gc.faceK (Gc.node (Gc.node a))
      have h6 : Gc.edge (Gc.edge (Gc.node (Gc.face (Gc.node (Gc.node a)))))
          = Gc.edge (Gc.node (Gc.node a)) := by rw [hk]
      rwa [hplainc.edge_edge] at h6
    have h7 : Gc.CFace (Gc.edge (Gc.node (Gc.node a))) (Gc.node a) := by
      have h8 := Gc.cface_face (Gc.edge (Gc.node (Gc.node a)))
      rwa [Gc.nodeK (Gc.node a)] at h8
    rw [hnb]
    exact h7.symm
  have hnxF : ∀ v ∈ (x :: p), Gc.CFace (Gc.node x) (Gc.node v) := by
    have key : ∀ (l : List Dc) (a : Dc), a ∈ (x :: p) → List.IsChain Gc.Rlink (a :: l) →
        (∀ w ∈ l, w ∈ (x :: p)) → ∀ w ∈ l, Gc.CFace (Gc.node a) (Gc.node w) := by
      intro l
      induction l with
      | nil => intro a _ _ _ w hw; exact absurd hw (by simp)
      | cons b l ih =>
        intro a ha hc hmem w hw
        have hab : Gc.Rlink a b := (List.isChain_cons_cons.mp hc).1
        have hbm : b ∈ (x :: p) := hmem b List.mem_cons_self
        have hnab : Gc.CFace (Gc.node a) (Gc.node b) := hnn a b ha hbm hab
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hnab
        · exact hnab.trans (ih b hbm (List.isChain_cons_cons.mp hc).2
            (fun t ht => hmem t (List.mem_cons_of_mem _ ht)) w hw)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact key p x List.mem_cons_self hchain (fun t ht => List.mem_cons_of_mem _ ht) v hv
  -- the node of the head is outside the kernel
  obtain ⟨y, hydef⟩ : ∃ t : Dc, t = p.getLastD x := ⟨_, rfl⟩
  have hpnil : p ≠ [] := by
    intro hc
    rw [hc] at hlen5
    simp at hlen5
  have hy_xp : y ∈ (x :: p) := by
    rw [hydef]; exact List.mem_cons_of_mem _ (getLastD_mem p x hpnil)
  have hkx : Gc.Kernel rc x := hker x List.mem_cons_self
  have hky : Gc.Kernel rc y := hker y hy_xp
  have hmapcons : (x :: p).map h = h x :: p.map h := by simp
  have hcych : IsCyclicChain Gm.Rlink (h x :: p.map h) := by
    rw [← hmapcons]; exact hURh.isCyclicChain
  have hhyRhx : Gm.Rlink (h y) (h x) := by
    have h1 := (isCyclicChain_cons.mp hcych).2
    rwa [getLast_cons_eq_getLastD, List.getLastD_map, ← hydef] at h1
  have hLhp : h x = Gm.face (Gm.face (Gm.edge (h y))) :=
    hFFE y x hy_xp List.mem_cons_self hhyRhx
  have hnf : ∀ w : Dm, Gm.node (Gm.face w) = Gm.edge w := by
    intro w
    have hk := Gm.faceK w
    have h9 : Gm.edge (Gm.edge (Gm.node (Gm.face w))) = Gm.edge w := by rw [hk]
    rwa [hplainm.edge_edge] at h9
  have hac_nx : ¬ Gc.Kernel rc (Gc.node x) := by
    intro hknx
    refine hLp ?_
    rw [← hydef]
    have hkenx : Gc.Kernel rc (Gc.edge (Gc.node x)) := by
      rw [← kernel_face, Gc.nodeK x]; exact hkx
    have hnxFny : Gc.CFace (Gc.node x) (Gc.node y) := hnxF y hy_xp
    have hkny : Gc.Kernel rc (Gc.node y) := (Kernel.congr hnxFny).mp hknx
    have hkeny : Gc.Kernel rc (Gc.edge (Gc.node y)) := by
      rw [← kernel_face, Gc.nodeK y]; exact hky
    have hnode : ∀ v : Dc, Gc.Kernel rc (Gc.node v) →
        Gc.Kernel rc (Gc.edge (Gc.node v)) → h (Gc.node v) = Gm.node (h v) := by
      intro v hknv hkenv
      have h1 : h (Gc.face (Gc.edge (Gc.node v))) = Gm.face (h (Gc.edge (Gc.node v))) :=
        hpre.face _ hkenv
      rw [Gc.nodeK v, embed_functor hemb hplainm hcubm hpre hknv hkenv] at h1
      have h2 : Gm.face (Gm.edge (h (Gc.node v))) = Gm.node (Gm.node (h (Gc.node v))) := by
        have hk := Gm.nodeK (Gm.node (Gm.node (h (Gc.node v))))
        rwa [hcubm.node_node_node] at hk
      rw [h2] at h1
      have h3 : Gm.node (h v) = h (Gc.node v) := by
        rw [h1, hcubm.node_node_node]
      exact h3.symm
    have hnx_eq : h (Gc.node x) = Gm.node (h x) := hnode x hknx hkenx
    have hny_eq : h (Gc.node y) = Gm.node (h y) := hnode y hkny hkeny
    have hfe : Gm.face (Gm.edge (h y)) = Gm.node (Gm.node (h y)) := by
      have hk := Gm.nodeK (Gm.node (Gm.node (h y)))
      rwa [hcubm.node_node_node] at hk
    have hkey : h (Gc.node y) = h (Gc.face (Gc.node x)) := by
      rw [hny_eq, hpre.face _ hknx, hnx_eq, hLhp, hfe, hnf, Gm.nodeK]
    have hnyF : Gc.CFace (Gc.node y) (Gc.face (Gc.node x)) :=
      hnxFny.symm.trans (Gc.cface_face (Gc.node x))
    have hny2 : Gc.node y = Gc.face (Gc.node x) := cface_inj_embed hpre hkny hnyF hkey
    have hybc : y ∉ rc := not_mem_of_kernel hky
    have hn3y : Gc.node (Gc.node (Gc.node y)) = y := hqc.node_node_node hybc
    have hfey : Gc.face (Gc.edge y) = Gc.node (Gc.node y) := by
      have hk := Gc.nodeK (Gc.node (Gc.node y))
      rwa [hn3y] at hk
    have hnny : Gc.node (Gc.node y) = Gc.edge (Gc.node x) := by
      rw [hny2]
      have hk := Gc.faceK (Gc.node x)
      have h9 : Gc.edge (Gc.edge (Gc.node (Gc.face (Gc.node x)))) = Gc.edge (Gc.node x) := by
        rw [hk]
      rwa [hplainc.edge_edge] at h9
    have h1 : Gc.CFace (Gc.edge y) (Gc.node (Gc.node y)) := by
      rw [← hfey]; exact Gc.cface_face (Gc.edge y)
    rw [hnny] at h1
    have h2 : Gc.CFace (Gc.edge (Gc.node x)) x := by
      have h3 := Gc.cface_face (Gc.edge (Gc.node x))
      rwa [Gc.nodeK x] at h3
    exact h1.trans h2
  -- five distinct darts of one face point into the kernel
  have hmemS : ∀ v ∈ (x :: p).map Gc.node,
      v ∈ {z : Dc | Gc.CFace (Gc.node x) z ∧ Gc.Kernel rc (Gc.edge z)} := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    refine ⟨hnxF w hw, ?_⟩
    rw [← kernel_face, Gc.nodeK w]
    exact hker w hw
  have hnd : ((x :: p).map Gc.node).Nodup := List.Nodup.map Gc.node.injective hnodup
  have hcard : ((x :: p).map Gc.node).toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen5]
  have hle : ((x :: p).map Gc.node).toFinset.card
      ≤ ({z : Dc | Gc.CFace (Gc.node x) z ∧ Gc.Kernel rc (Gc.edge z)}).ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro v hv
    exact hmemS v (List.mem_toFinset.mp hv)
  have h4 := adj_kernel_max hemb hpre hac_nx
  omega

/-- **The five-dart step of `embed_full`**: a homomorphic ring whose image
bounds at most one face — at most none if it has fewer than five darts — closes
up. -/
private theorem embed_full_ring5 (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} {p : List Dc}
    (hring : PreHomRing Gc Gm rc h x p)
    (hF : Gm.faceCard (Gm.DiskF ((x :: p).map h))
      ≤ (if (x :: p).length = 5 then 1 else 0)) :
    Gc.Rlink (p.getLastD x) x := by
  classical
  by_contra hLp
  refine hLp (trivial_hom_ring hemb hplanm hplainm hbridgem hconnm hcubm hpre hring ?_)
  by_cases h5 : (x :: p).length = 5
  · refine embed_full_noface hemb hplanm hplainm hbridgem hcubm hBm hpentm hpre hring hLp h5 ?_
    have hite : (if (x :: p).length = 5 then (1 : ℕ) else 0) = 1 := by
      split_ifs
      rfl
    rw [hite] at hF
    exact hF
  · intro u hu
    have hite : (if (x :: p).length = 5 then (1 : ℕ) else 0) = 0 := by
      split_ifs
      rfl
    rw [hite] at hF
    have h2 : 0 < Gm.faceCard (Gm.DiskF ((x :: p).map h)) := zero_lt_faceCard.mpr ⟨u, hu⟩
    omega

omit [Finite Dc] [Finite Dm] in
/-- The reverse ring of an R-link path is an R-link path. -/
private theorem isChain_revRing (hplainc : Gc.Plain) {l : List Dc}
    (hc : List.IsChain Gc.Rlink l) : List.IsChain Gc.Rlink (Gc.revRing l) := by
  rw [revRing, List.isChain_reverse, List.isChain_map]
  refine hc.imp ?_
  intro a b hab
  change Gc.CFace (Gc.edge (Gc.edge b)) (Gc.edge a)
  rw [hplainc.edge_edge]
  exact hab.symm

omit [Finite Dm] in
/-- The preembedding carries the reverse ring of a path in the kernel to the
reverse ring of its image. -/
private theorem map_revRing_embed (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (l : List Dc)
    (hk : ∀ z ∈ l, Gc.Kernel rc z) (hke : ∀ z ∈ l, Gc.Kernel rc (Gc.edge z)) :
    (Gc.revRing l).map h = Gm.revRing (l.map h) := by
  simp only [revRing, List.map_reverse, List.map_map]
  congr 1
  exact List.map_congr_left fun z hz =>
    embed_functor hemb hplainm hcubm hpre (hk z hz) (hke z hz)

omit [Finite Dm] in
/-- The reverse ring of a list extended on the right. -/
private theorem revRing_concat (M : List Dm) (t : Dm) :
    Gm.revRing (M ++ [t]) = Gm.edge t :: Gm.revRing M := by
  simp [revRing]

/-- **The reverse-ring step of `embed_full`**: a homomorphic ring of at most
five darts closes up.  If it did not, then both it and the reverse ring built
from its edges would bound too many faces, which Birkhoff's lemma forbids. -/
private theorem embed_full_ring4 (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} {p : List Dc}
    (hring : PreHomRing Gc Gm rc h x p) (hlen : p.length ≤ 4) :
    Gc.Rlink (p.getLastD x) x := by
  classical
  by_contra hLp
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hchain := hring.chain
  have hker := hring.kernel
  have hURh := hring.scycle
  have hkx : Gc.Kernel rc x := hker x List.mem_cons_self
  have hpnil : p ≠ [] := by
    rintro rfl
    have h1 : Gm.Rlink (h x) (h x) := by simpa using hURh.isCyclicChain
    exact hbridgem (h x) h1.symm
  obtain ⟨p1, y, hp⟩ : ∃ p1 y, p = p1 ++ [y] :=
    ⟨p.dropLast, p.getLast hpnil, (List.dropLast_append_getLast hpnil).symm⟩
  have hy : p.getLastD x = y := by rw [hp]; exact List.getLastD_concat
  have hky : Gc.Kernel rc y := hker y (by rw [hp]; simp)
  -- the image ring is a proper ring
  have hproper : Gm.ProperRing ((x :: p).map h) := by
    by_cases hp1 : p1 = []
    · subst hp1
      rw [hp] at hchain ⊢
      simp only [List.nil_append, List.map_cons, List.map_nil, properRing_pair]
      intro hcon
      refine hLp ?_
      rw [hy]
      have hRxy : Gc.Rlink x y := (List.isChain_cons_cons.mp hchain).1
      have hkex : Gc.Kernel rc (Gc.edge x) := (Kernel.congr hRxy).mpr hky
      have h2 : h (Gc.edge x) = h y := by
        rw [embed_functor hemb hplainm hcubm hpre hkx hkex, hcon]
      have h3 : Gc.edge x = y := cface_inj_embed hpre hkex hRxy h2
      change Gc.CFace (Gc.edge y) x
      rw [← h3, hplainc.edge_edge]
    · refine Gm.properRing_of_two_lt_length ?_
      rw [List.length_map, hp]
      simp only [List.length_cons, List.length_append]
      have h1 : p1.length ≠ 0 := fun hc => hp1 (List.length_eq_zero_iff.mp hc)
      omega
  -- every dart but the last has its edge in the kernel
  have hkedge : ∀ z ∈ (x :: p1), Gc.Kernel rc (Gc.edge z) := by
    have key : ∀ (l : List Dc) (a b : Dc), List.IsChain Gc.Rlink (a :: (l ++ [b])) →
        (∀ w ∈ (a :: (l ++ [b])), Gc.Kernel rc w) →
        ∀ z ∈ (a :: l), Gc.Kernel rc (Gc.edge z) := by
      intro l
      induction l with
      | nil =>
        intro a b hc hk z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (Kernel.congr (List.isChain_cons_cons.mp hc).1).mpr (hk b (by simp))
        · exact absurd hz (by simp)
      | cons c l ih =>
        intro a b hc hk z hz
        have hac : Gc.Rlink a c := (List.isChain_cons_cons.mp hc).1
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (Kernel.congr hac).mpr (hk c (by simp))
        · exact ih c b (List.isChain_cons_cons.mp hc).2
            (fun w hw => hk w (List.mem_cons_of_mem _ hw)) z hz
    intro z hz
    refine key p1 x y (by rw [← hp]; exact hchain) (fun w hw => hker w ?_) z hz
    rw [hp]; exact hw
  -- the dart matching the closing link of the image ring
  have hmapcons : (x :: p).map h = h x :: p.map h := by simp
  have hcych : IsCyclicChain Gm.Rlink (h x :: p.map h) := by
    rw [← hmapcons]; exact hURh.isCyclicChain
  have hhyRhx : Gm.Rlink (h y) (h x) := by
    have h1 := (isCyclicChain_cons.mp hcych).2
    rwa [getLast_cons_eq_getLastD, List.getLastD_map, hy] at h1
  obtain ⟨ry, hxry, hry⟩ : ∃ t, Gc.CFace x t ∧ h t = Gm.edge (h y) :=
    exists_cface_h hpre hkx hhyRhx.symm
  -- the reverse ring
  have hrev_eq : Gc.revRing (x :: p1) = (p1.map Gc.edge).reverse ++ [Gc.edge x] := by
    simp [revRing]
  obtain ⟨rx, rp, hrxp⟩ : ∃ rx rp, Gc.revRing (x :: p1) ++ [ry] = rx :: rp := by
    cases hd : Gc.revRing (x :: p1) ++ [ry] with
    | nil => exact absurd hd (by simp)
    | cons a l => exact ⟨a, l, rfl⟩
  have hlen_rxp : (rx :: rp).length = p.length + 1 := by
    rw [← hrxp, hp]
    simp [revRing]
  have hrp_len : rp.length = p.length := by
    simp only [List.length_cons] at hlen_rxp
    omega
  have hlen_eq : (rx :: rp).length = (x :: p).length := by
    simp only [List.length_cons]
    omega
  -- the reverse ring is an R-link path in the kernel
  have hchain_rev : List.IsChain Gc.Rlink (Gc.revRing (x :: p1)) :=
    isChain_revRing hplainc (hchain.prefix ⟨[y], by rw [hp]; simp⟩)
  have hchain_rxp : List.IsChain Gc.Rlink (rx :: rp) := by
    rw [← hrxp]
    refine hchain_rev.append (List.isChain_singleton _) ?_
    intro a ha b hb
    rw [hrev_eq, List.getLast?_concat, Option.mem_def, Option.some.injEq] at ha
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst ha; subst hb
    change Gc.CFace (Gc.edge (Gc.edge x)) ry
    rw [hplainc.edge_edge]
    exact hxry
  have hker_rxp : ∀ w ∈ (rx :: rp), Gc.Kernel rc w := by
    rw [← hrxp]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · have h1 : Gc.edge w ∈ (x :: p1) := (mem_revRing hplainc).mp hw
      have h2 : Gc.Kernel rc (Gc.edge (Gc.edge w)) := hkedge (Gc.edge w) h1
      rwa [hplainc.edge_edge] at h2
    · simp only [List.mem_singleton] at hw
      rw [hw]
      exact (Kernel.congr hxry).mp hkx
  -- the image of the reverse ring is a rotation of the reverse image ring
  have hmap' : (rx :: rp).map h = (Gm.revRing ((x :: p).map h)).rotate 1 := by
    rw [← hrxp]
    have h1 : (x :: p).map h = ((x :: p1).map h) ++ [h y] := by rw [hp]; simp
    rw [h1, revRing_concat, List.map_append,
      map_revRing_embed hemb hplainm hcubm hpre (x :: p1)
        (fun z hz => hker z (by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (by rw [hp]; exact List.mem_append_left _ hz)))
        hkedge]
    simp [hry]
  have hscyc_rev : Gm.Scycle Gm.Rlink (Gm.revRing ((x :: p).map h)) :=
    scycle_revRing hplainm hURh
  have hsimple_rxp : Gm.Simple ((rx :: rp).map h) := by
    rw [hmap']
    exact simple_rotate.mpr hscyc_rev.simple
  have hcyc_rxp : IsCyclicChain Gm.Rlink ((rx :: rp).map h) := by
    rw [hmap']
    exact isCyclicChain_rotate.mpr hscyc_rev.isCyclicChain
  have hmapcons2 : (rx :: rp).map h = h rx :: rp.map h := by simp
  have hGmlast : Gm.Rlink (h (rp.getLastD rx)) (h rx) := by
    have h1 : IsCyclicChain Gm.Rlink (h rx :: rp.map h) := by
      rw [← hmapcons2]; exact hcyc_rxp
    have h2 := (isCyclicChain_cons.mp h1).2
    rwa [getLast_cons_eq_getLastD, List.getLastD_map] at h2
  have hring_rev : PreHomRing Gc Gm rc h rx rp :=
    intro_preHomRing hemb hplainm hcubm hpre hchain_rxp hGmlast hker_rxp hsimple_rxp
  -- the reverse ring does not close up either
  have hlast_rp : rp.getLastD rx = ry := by
    have h1 : (rx :: rp).getLastD ry = ry := by
      rw [← hrxp]; exact List.getLastD_concat
    rwa [List.getLastD_cons] at h1
  have hrx : rx = Gc.edge (p1.getLastD x) := by
    have h1 : rp.reverse ++ [rx] = ry :: ((x :: p1).map Gc.edge) := by
      have h2 : (rx :: rp).reverse = (Gc.revRing (x :: p1) ++ [ry]).reverse := by rw [hrxp]
      simpa [revRing] using h2
    have h3 : (rp.reverse ++ [rx]).getLastD ry = rx := List.getLastD_concat
    rw [h1, List.getLastD_cons, List.map_cons, List.getLastD_cons, List.getLastD_map] at h3
    exact h3.symm
  have hcf_rx_y : Gc.CFace rx y := by
    have h3 : List.IsChain Gc.Rlink ((x :: p1) ++ [y]) := by
      rw [show (x :: p1) ++ [y] = x :: (p1 ++ [y]) by simp, ← hp]
      exact hchain
    have h4 := (List.isChain_append.mp h3).2.2
    have h5 := h4 ((x :: p1).getLast (List.cons_ne_nil x p1))
      (by rw [Option.mem_def]; exact List.getLast?_eq_some_getLast _) y (by simp)
    rw [getLast_cons_eq_getLastD] at h5
    rw [hrx]
    exact h5
  have hLp_rev : ¬ Gc.Rlink (rp.getLastD rx) rx := by
    rw [hlast_rp]
    intro hryrx
    have hryy : Gc.Rlink ry y := hryrx.trans hcf_rx_y
    refine hLp ?_
    rw [hy]
    have hkry : Gc.Kernel rc ry := (Kernel.congr hxry).mp hkx
    have hkery : Gc.Kernel rc (Gc.edge ry) := (Kernel.congr hryy).mpr hky
    have hDhy : h (Gc.edge ry) = h y := by
      rw [embed_functor hemb hplainm hcubm hpre hkry hkery, hry, hplainm.edge_edge]
    have hery : Gc.edge ry = y := cface_inj_embed hpre hkery hryy hDhy
    change Gc.CFace (Gc.edge y) x
    rw [← hery, hplainc.edge_edge]
    exact hxry.symm
  -- both sides of the image ring carry too many faces
  have hm : ¬ (Gm.faceCard (Gm.DiskF ((x :: p).map h))
      ≤ (if (x :: p).length = 5 then 1 else 0)) := fun hc =>
    hLp (embed_full_ring5 hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hring hc)
  have hm2 : ¬ (Gm.faceCard (Gm.DiskF ((rx :: rp).map h))
      ≤ (if (rx :: rp).length = 5 then 1 else 0)) := fun hc =>
    hLp_rev (embed_full_ring5 hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
      hring_rev hc)
  rw [hlen_eq] at hm2
  have hfc : Gm.faceCard (Gm.DiskF ((rx :: rp).map h))
      = Gm.faceCard (Gm.DiskFC ((x :: p).map h)) := by
    refine faceCard_congr fun v => ?_
    rw [hmap', diskF_rotate, diskF_revRing hplanm hplainm hconnm hURh hproper]
  rw [hfc] at hm2
  have hlenr : ((x :: p).map h).length = (x :: p).length := by simp
  refine hBm ((x :: p).map h) ?_ hURh ?_
  · rw [hlenr]
    simp only [List.length_cons]
    omega
  · rw [hlenr]
    exact ⟨by omega, by omega⟩

/-- **The loop-removal step of `embed_full`**: an R-link path in the kernel can
be shortened, keeping its endpoints, until its image is face-simple.  The loops
that are cut out are ruled out by `Hypermap.embed_full_ring4`. -/
private theorem embed_full_simplify (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) :
    ∀ (p : List Dc) (x0 : Dc), List.IsChain Gc.Rlink (x0 :: p) →
      (∀ z ∈ p, Gc.Kernel rc z) → p.length ≤ 5 →
      ∃ q : List Dc, List.IsChain Gc.Rlink (x0 :: q) ∧ q.getLastD x0 = p.getLastD x0 ∧
        (∀ z ∈ q, Gc.Kernel rc z) ∧ Gm.Simple (q.map h) ∧ q.length ≤ p.length := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  intro p
  induction p with
  | nil =>
    intro x0 _ _ _
    exact ⟨[], List.isChain_singleton _, rfl, by simp, by simp, le_rfl⟩
  | cons x1 p' ih =>
    intro x0 hchain hkp hlen
    have hx0x1 : Gc.Rlink x0 x1 := (List.isChain_cons_cons.mp hchain).1
    have hchain' : List.IsChain Gc.Rlink (x1 :: p') := (List.isChain_cons_cons.mp hchain).2
    have hkx1 : Gc.Kernel rc x1 := hkp x1 List.mem_cons_self
    have hkp' : ∀ z ∈ p', Gc.Kernel rc z := fun z hz => hkp z (List.mem_cons_of_mem _ hz)
    have hlen' : p'.length ≤ 5 := by simp only [List.length_cons] at hlen; omega
    obtain ⟨q, hq_chain, hq_last, hq_ker, hq_simple, hq_len⟩ := ih x1 hchain' hkp' hlen'
    by_cases hband : Gm.Fband (q.map h) (h x1)
    · obtain ⟨w, hw, hcfw⟩ := hband
      obtain ⟨x2, hx2q, rfl⟩ := List.mem_map.mp hw
      have hkx2 : Gc.Kernel rc x2 := hq_ker x2 hx2q
      obtain ⟨x3, hx2x3, hhx3⟩ : ∃ t, Gc.CFace x2 t ∧ h t = h x1 :=
        exists_cface_h hpre hkx2 hcfw.symm
      have hkx3 : Gc.Kernel rc x3 := (Kernel.congr hx2x3).mp hkx2
      obtain ⟨q1, q2, hqsplit⟩ := List.append_of_mem hx2q
      have hqlen : q.length = q1.length + (q2.length + 1) := by rw [hqsplit]; simp
      have hq_chain2 : List.IsChain Gc.Rlink (x1 :: (q1 ++ x2 :: q2)) := by
        rw [← hqsplit]; exact hq_chain
      by_cases hx13 : x1 = x3
      · refine ⟨x2 :: q2, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.isChain_cons_cons.mpr ⟨?_, ?_⟩
          · change Gc.CFace (Gc.edge x0) x2
            refine hx0x1.trans ?_
            rw [hx13]
            exact hx2x3.symm
          · exact hq_chain2.suffix ⟨x1 :: q1, by simp⟩
        · rw [List.getLastD_cons, List.getLastD_cons, ← hq_last, hqsplit,
            getLastD_append_cons]
        · intro z hz
          refine hq_ker z ?_
          rw [hqsplit]
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_append_right _ List.mem_cons_self
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hz)
        · have h1 : q.map h = (q1.map h) ++ ((x2 :: q2).map h) := by rw [hqsplit]; simp
          rw [h1] at hq_simple
          exact (simple_append.mp hq_simple).2.1
        · simp only [List.length_cons]
          omega
      · exfalso
        rcases q1 with _ | ⟨xx, q''⟩
        · have hRx1x2 : Gc.Rlink x1 x2 := by
            have h1 : List.IsChain Gc.Rlink (x1 :: ([] ++ x2 :: q2)) := hq_chain2
            exact (List.isChain_cons_cons.mp h1).1
          have hkex1 : Gc.Kernel rc (Gc.edge x1) := (Kernel.congr hRx1x2).mpr hkx2
          have h2 : Gm.CFace (h (Gc.edge x1)) (h x2) := cface_h hpre hkex1 hRx1x2
          rw [embed_functor hemb hplainm hcubm hpre hkx1 hkex1] at h2
          exact hbridgem (h x1) ((h2.trans hcfw.symm).symm)
        · have hpref : List.IsChain Gc.Rlink (x1 :: (xx :: (q'' ++ [x2]))) :=
            hq_chain2.prefix ⟨q2, by simp⟩
          have hRx1xx : Gc.Rlink x1 xx := (List.isChain_cons_cons.mp hpref).1
          have hchain_xx : List.IsChain Gc.Rlink (xx :: (q'' ++ [x2])) :=
            (List.isChain_cons_cons.mp hpref).2
          have hkxx : Gc.Kernel rc xx := hq_ker xx (by rw [hqsplit]; simp)
          have hkex1 : Gc.Kernel rc (Gc.edge x1) := (Kernel.congr hRx1xx).mpr hkxx
          have hq''sub : ∀ z ∈ q'', z ∈ q := by
            intro z hz
            rw [hqsplit]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ hz)
          -- the shortened ring
          have hchain_new : List.IsChain Gc.Rlink (xx :: (q'' ++ [x3])) := by
            have h1 : xx :: (q'' ++ [x2]) = (xx :: q'') ++ [x2] := by simp
            rw [h1] at hchain_xx
            obtain ⟨hc1, -, hc3⟩ := List.isChain_append.mp hchain_xx
            have h2 : xx :: (q'' ++ [x3]) = (xx :: q'') ++ [x3] := by simp
            rw [h2]
            refine hc1.append (List.isChain_singleton _) ?_
            intro a ha b hb
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
            subst hb
            exact (hc3 a ha x2 (by simp)).trans hx2x3
          have hker_new : ∀ z ∈ (xx :: (q'' ++ [x3])), Gc.Kernel rc z := by
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact hkxx
            · rcases List.mem_append.mp hz with hz | hz
              · exact hq_ker z (hq''sub z hz)
              · simp only [List.mem_singleton] at hz
                rw [hz]; exact hkx3
          have hlast_new : Gm.Rlink (h ((q'' ++ [x3]).getLastD xx)) (h xx) := by
            rw [List.getLastD_concat, hhx3]
            change Gm.CFace (Gm.edge (h x1)) (h xx)
            rw [← embed_functor hemb hplainm hcubm hpre hkx1 hkex1]
            exact cface_h hpre hkex1 hRx1xx
          have hsimple_new : Gm.Simple ((xx :: (q'' ++ [x3])).map h) := by
            have h1 : q.map h = ((xx :: (q'' ++ [x2])).map h) ++ (q2.map h) := by
              rw [hqsplit]; simp
            rw [h1] at hq_simple
            have h2 := (simple_append.mp hq_simple).1
            have h3 : (xx :: (q'' ++ [x2])).map h = ((xx :: q'').map h) ++ [h x2] := by simp
            rw [h3, simple_concat] at h2
            have h4 : (xx :: (q'' ++ [x3])).map h = ((xx :: q'').map h) ++ [h x3] := by simp
            rw [h4, simple_concat]
            refine ⟨fun hb => h2.1 ((Fband.congr ?_).mp hb), h2.2⟩
            rw [hhx3]
            exact hcfw
          have hring_new : PreHomRing Gc Gm rc h xx (q'' ++ [x3]) :=
            intro_preHomRing hemb hplainm hcubm hpre hchain_new hlast_new hker_new hsimple_new
          have hlen_new : (q'' ++ [x3]).length ≤ 4 := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hqlen ⊢
            simp only [List.length_cons] at hlen
            omega
          have hRx3xx := embed_full_ring4 hemb hplanm hplainm hbridgem hconnm hcubm hBm
            hpentm hpre hring_new hlen_new
          rw [List.getLastD_concat] at hRx3xx
          -- both `edge x1` and `edge x3` reach `xx`
          have hcf13 : Gc.CFace (Gc.edge x1) (Gc.edge x3) := hRx1xx.trans hRx3xx.symm
          have hkex3 : Gc.Kernel rc (Gc.edge x3) := (Kernel.congr hcf13).mp hkex1
          have heq : h (Gc.edge x1) = h (Gc.edge x3) := by
            rw [embed_functor hemb hplainm hcubm hpre hkx1 hkex1,
              embed_functor hemb hplainm hcubm hpre hkx3 hkex3, hhx3]
          have h5 : Gc.edge x1 = Gc.edge x3 := cface_inj_embed hpre hkex1 hcf13 heq
          exact hx13 (Gc.edge.injective h5)
    · refine ⟨x1 :: q, List.isChain_cons_cons.mpr ⟨hx0x1, hq_chain⟩, ?_, ?_, ?_, ?_⟩
      · rw [List.getLastD_cons, List.getLastD_cons]; exact hq_last
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hkx1
        · exact hq_ker z hz
      · rw [List.map_cons, simple_cons]
        exact ⟨hband, hq_simple⟩
      · simp only [List.length_cons]
        omega

/-- **The path step of `embed_full`**: a short R-link path in the kernel whose
image closes up under `edge` already closes up. -/
private theorem embed_full_path (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x0 : Dc} {p : List Dc}
    (hchain : List.IsChain Gc.Rlink (x0 :: p)) (hkp : ∀ z ∈ p, Gc.Kernel rc z)
    (hLhp : Gm.edge (h (p.getLastD x0)) = h (Gc.edge x0)) (hlen : p.length ≤ 5) :
    p.getLastD x0 = x0 := by
  classical
  obtain ⟨q, hq_chain, hq_last, hq_ker, hq_simple, hq_len⟩ :=
    embed_full_simplify hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre p x0
      hchain hkp hlen
  rcases q with _ | ⟨xq, q'⟩
  · exact hq_last.symm
  · have hkxq : Gc.Kernel rc xq := hq_ker xq List.mem_cons_self
    have hx0xq : Gc.Rlink x0 xq := (List.isChain_cons_cons.mp hq_chain).1
    have hchainq : List.IsChain Gc.Rlink (xq :: q') := (List.isChain_cons_cons.mp hq_chain).2
    have hLq : q'.getLastD xq = p.getLastD x0 := by
      rw [← hq_last, List.getLastD_cons]
    have hkex0 : Gc.Kernel rc (Gc.edge x0) := (Kernel.congr hx0xq).mpr hkxq
    have hGmlast : Gm.Rlink (h (q'.getLastD xq)) (h xq) := by
      rw [hLq]
      change Gm.CFace (Gm.edge (h (p.getLastD x0))) (h xq)
      rw [hLhp]
      exact cface_h hpre hkex0 hx0xq
    have hring : PreHomRing Gc Gm rc h xq q' :=
      intro_preHomRing hemb hplainm hcubm hpre hchainq hGmlast hq_ker hq_simple
    have hlen4 : q'.length ≤ 4 := by
      simp only [List.length_cons] at hq_len
      omega
    have hR := embed_full_ring4 hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
      hring hlen4
    rw [hLq] at hR
    have hkL : Gc.Kernel rc (p.getLastD x0) := by
      rw [← hLq]
      have h1 := getLastD_mem (xq :: q') xq (by simp)
      rw [List.getLastD_cons] at h1
      exact hq_ker _ h1
    have hkeL : Gc.Kernel rc (Gc.edge (p.getLastD x0)) := (Kernel.congr hR).mpr hkxq
    have hcfL : Gc.CFace (Gc.edge (p.getLastD x0)) (Gc.edge x0) := hR.trans hx0xq.symm
    have hheq : h (Gc.edge (p.getLastD x0)) = h (Gc.edge x0) := by
      rw [embed_functor hemb hplainm hcubm hpre hkL hkeL, hLhp]
    exact Gc.edge.injective (cface_inj_embed hpre hkeL hcfL hheq)

/-- **The preembedding reflects E-links.**  This is the reference's
`embed_full`: if the images of two kernel darts are E-linked, so are the darts
themselves. -/
theorem embed_full (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x1 x2 : Dc}
    (hk1 : Gc.Kernel rc x1) (hk2 : Gc.Kernel rc x2) (heq : Gm.edge (h x1) = h x2) :
    Gc.edge x1 = x2 := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  obtain ⟨x0, hk0, hrad⟩ := hemb.kernel
  have hAface : ∀ z : Dc, Gc.face z ∈ {w : Dc | Gc.Kernel rc w} ↔ z ∈ {w : Dc | Gc.Kernel rc w} :=
    fun _ => kernel_face
  obtain ⟨x01, x10, hx0x01, hx1x10, hke01, hcf01⟩ :=
    (atRadius2_iff hAface).mp (hrad x1 hk1)
  obtain ⟨x02, x20, hx0x02, hx2x20, hke02, hcf02⟩ :=
    (atRadius2_iff hAface).mp (hrad x2 hk2)
  have hk01 : Gc.Kernel rc (Gc.edge x01) := hke01
  have hk02 : Gc.Kernel rc (Gc.edge x02) := hke02
  have hk0' : Gc.Kernel rc x0 := hk0
  -- the five-dart path from `edge x1` to `x2`
  have hchain : List.IsChain Gc.Rlink
      (Gc.edge x1 :: [x10, Gc.edge x01, x02, Gc.edge x20, x2]) := by
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
      List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
        List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩⟩⟩⟩
    · change Gc.CFace (Gc.edge (Gc.edge x1)) x10
      rw [hplainc.edge_edge]
      exact hx1x10
    · exact hcf01.symm
    · change Gc.CFace (Gc.edge (Gc.edge x01)) x02
      rw [hplainc.edge_edge]
      exact hx0x01.symm.trans hx0x02
    · exact hcf02
    · change Gc.CFace (Gc.edge (Gc.edge x20)) x2
      rw [hplainc.edge_edge]
      exact hx2x20.symm
  have hkp : ∀ z ∈ [x10, Gc.edge x01, x02, Gc.edge x20, x2], Gc.Kernel rc z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact (Kernel.congr hx1x10).mp hk1
    · exact hk01
    · exact (Kernel.congr hx0x02).mp hk0'
    · exact (Kernel.congr hcf02).mp hk02
    · exact hk2
  have hlast : ([x10, Gc.edge x01, x02, Gc.edge x20, x2]).getLastD (Gc.edge x1) = x2 := rfl
  have hLhp : Gm.edge (h (([x10, Gc.edge x01, x02, Gc.edge x20, x2]).getLastD (Gc.edge x1)))
      = h (Gc.edge (Gc.edge x1)) := by
    rw [hlast, ← heq, hplainm.edge_edge, hplainc.edge_edge]
  have hres := embed_full_path hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
    hchain hkp hLhp (by simp)
  rw [hlast] at hres
  exact hres.symm

end EmbedFull

/-! ### Injectivity and the morphism laws

With `Hypermap.embed_full` in hand the preembedding is injective on the kernel,
and its extension `Hypermap.embed` is a morphism for `edge` everywhere and for
`node` off the perimeter. -/

section EmbedMorph

/-- **The preembedding is injective on the kernel.**  This is the reference's
`pre_embed_inj`. -/
theorem pre_embed_inj (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x y : Dc}
    (hkx : Gc.Kernel rc x) (hky : Gc.Kernel rc y) (heq : h x = h y) : x = y := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hkA : ∀ u v : Dc, Gc.CFace u v → u ∈ {z : Dc | Gc.Kernel rc z} →
      v ∈ {z : Dc | Gc.Kernel rc z} := fun u v huv hu => (Kernel.congr huv).mp hu
  have hkeex : Gc.edge (Gc.edge x) ∈ {z : Dc | Gc.Kernel rc z} := by
    change Gc.Kernel rc (Gc.edge (Gc.edge x))
    rw [hplainc.edge_edge]
    exact hkx
  obtain ⟨q, hqne, hqchain, hqlast, hqsimple, hqmem⟩ := hpre.simple_path hkA hkeex hky
  rcases q with _ | ⟨z1, q'⟩
  · exact absurd rfl hqne
  · have hxz1 : Gc.CFace x z1 := by
      have h2 : Gc.CFace (Gc.edge (Gc.edge x)) z1 := (List.isChain_cons_cons.mp hqchain).1
      rwa [hplainc.edge_edge] at h2
    rcases q' with _ | ⟨z2, q''⟩
    · have hz1y : Gc.CFace z1 y := by
        rwa [List.getLastD_cons, List.getLastD_nil] at hqlast
      exact cface_inj_embed hpre hkx (hxz1.trans hz1y) heq
    · have hz1z2 : Gc.Rlink z1 z2 :=
        (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hqchain).2).1
      have hkz1 : Gc.Kernel rc z1 := (hqmem z1 List.mem_cons_self).1
      have hcz1 : EdgeCentral Gc Gm h z1 := (hqmem z1 List.mem_cons_self).2
      have hkz2 : Gc.Kernel rc z2 :=
        (hqmem z2 (List.mem_cons_of_mem _ List.mem_cons_self)).1
      have hkez1 : Gc.Kernel rc (Gc.edge z1) := (Kernel.congr hz1z2).mpr hkz2
      have hcfhx : Gm.CFace (h x) (h z1) := cface_h hpre hkx hxz1
      rw [heq] at hcfhx
      obtain ⟨t, hyt, hht⟩ := exists_cface_h hpre hky hcfhx
      have hkt : Gc.Kernel rc t := (Kernel.congr hyt).mp hky
      have hfull : Gc.edge t = Gc.edge z1 := by
        refine embed_full hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hkt
          hkez1 ?_
        rw [hht]
        exact hcz1.symm
      have htz1 : t = z1 := Gc.edge.injective hfull
      refine cface_inj_embed hpre hkx (hxz1.trans ?_) heq
      rw [← htz1]
      exact hyt.symm

omit [Finite Dm] in
/-- **The embedding commutes with `edge`.**  This is the reference's
`embedE`. -/
theorem embedE (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (x : Dc) :
    embed Gc Gm rc h (Gc.edge x) = Gm.edge (embed Gc Gm rc h x) := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hfem : ∀ u : Dm, Gm.face (Gm.edge u) = Gm.node (Gm.node u) := by
    intro u
    have hk := Gm.nodeK (Gm.node (Gm.node u))
    rwa [hcubm.node_node_node u] at hk
  have key : ∀ z : Dc, z ∉ rc →
      embed Gc Gm rc h (Gc.edge z) = Gm.edge (embed Gc Gm rc h z) := by
    intro z hzbc
    have h3 : Gc.edge (Gc.edge z) = z := hplainc.edge_edge z
    by_cases hkz : Gc.Kernel rc z
    · by_cases hkez : Gc.Kernel rc (Gc.edge z)
      · rw [embed_of_kernel hkez, embed_of_kernel hkz]
        exact embed_functor hemb hplainm hcubm hpre hkz hkez
      · rw [embed_of_kernel_edge hkez (by rw [h3]; exact hkz), embed_of_kernel hkz, h3]
    · by_cases hkez : Gc.Kernel rc (Gc.edge z)
      · rw [embed_of_kernel hkez, embed_of_kernel_edge hkz hkez, hplainm.edge_edge]
      · have hnotboth : ¬ Gc.Kernel rc (Gc.node (Gc.edge z)) := by
          intro hc
          have h1 : Gc.node (Gc.edge z) ∉ rc := not_mem_of_kernel hc
          have h2 : Gc.edge z ∉ rc := fun hm => h1 ((node_mem_ring_iff hemb _).mpr hm)
          rcases chordless_perimeter hemb hpre hzbc h2 with hk | hk
          · exact hkz hk
          · exact hkez hk
        have hknz : Gc.Kernel rc (Gc.node z) := by
          rcases embed_cases hemb hpre z with hc | hc
          · exact absurd hc (by rw [not_or]; exact ⟨hkz, hkez⟩)
          · exact hc.resolve_right hnotboth
        rw [embed_of_kernel_node_edge hkez (by rw [h3]; exact hkz) hnotboth,
          embed_of_kernel_node hkz hkez hknz, h3, hfem]
  rcases edge_perimeter hemb x with hbc | hbc
  · exact key x hbc
  · have h1 := key (Gc.edge x) hbc
    rw [hplainc.edge_edge] at h1
    rw [h1, hplainm.edge_edge]

omit [Finite Dm] in
/-- **The embedding commutes with `node` off the perimeter.**  This is the
reference's `embedN`. -/
theorem embedN (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dc} (hxbc : x ∉ rc) :
    embed Gc Gm rc h (Gc.node x) = Gm.node (embed Gc Gm rc h x) := by
  classical
  have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
  have hn3x : Gc.node (Gc.node (Gc.node x)) = x := hqc.node_node_node hxbc
  have hfec : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
    have hk := Gc.nodeK (Gc.node (Gc.node x))
    rwa [hn3x] at hk
  have hfem : ∀ u : Dm, Gm.face (Gm.edge u) = Gm.node (Gm.node u) := by
    intro u
    have hk := Gm.nodeK (Gm.node (Gm.node u))
    rwa [hcubm.node_node_node u] at hk
  have hnfm : ∀ u : Dm, Gm.node (Gm.face u) = Gm.edge u := by
    intro u
    have hk := Gm.faceK u
    have h9 : Gm.edge (Gm.edge (Gm.node (Gm.face u))) = Gm.edge u := by rw [hk]
    rwa [hplainm.edge_edge] at h9
  have hkenx : Gc.Kernel rc (Gc.edge (Gc.node x)) ↔ Gc.Kernel rc x := by
    rw [← kernel_face, Gc.nodeK x]
  have hknnx : Gc.Kernel rc (Gc.node (Gc.node x)) ↔ Gc.Kernel rc (Gc.edge x) := by
    rw [← hfec, kernel_face]
  by_cases hA : Gc.Kernel rc x
  · rw [embed_of_kernel hA]
    have hkenx' : Gc.Kernel rc (Gc.edge (Gc.node x)) := hkenx.mpr hA
    have h1 := hpre.face _ hkenx'
    rw [Gc.nodeK x] at h1
    by_cases hC : Gc.Kernel rc (Gc.node x)
    · rw [embed_of_kernel hC]
      rw [embed_functor hemb hplainm hcubm hpre hC hkenx', hfem] at h1
      rw [h1, hcubm.node_node_node]
    · rw [embed_of_kernel_edge hC hkenx', h1, hnfm]
  · by_cases hB : Gc.Kernel rc (Gc.edge x)
    · rw [embed_of_kernel_edge hA hB]
      have h2 : h (Gc.node (Gc.node x)) = Gm.face (h (Gc.edge x)) := by
        have h3 := hpre.face _ hB
        rwa [hfec] at h3
      by_cases hC : Gc.Kernel rc (Gc.node x)
      · rw [embed_of_kernel hC]
        have hkennx : Gc.Kernel rc (Gc.edge (Gc.node (Gc.node x))) := by
          rw [← kernel_face, Gc.nodeK (Gc.node x)]
          exact hC
        have h1 := hpre.face _ hkennx
        rw [Gc.nodeK (Gc.node x),
          embed_functor hemb hplainm hcubm hpre (hknnx.mpr hB) hkennx, hfem] at h1
        rw [h1, h2, hnfm]
      · rw [embed_of_kernel_node hC (fun hc => hA (hkenx.mp hc)) (hknnx.mpr hB), h2, hfem,
          hnfm]
    · have hnotnex : ¬ Gc.Kernel rc (Gc.node (Gc.edge x)) := by
        intro hc
        have h1 : Gc.node (Gc.edge x) ∉ rc := not_mem_of_kernel hc
        have h2 : Gc.edge x ∉ rc := fun hm => h1 ((node_mem_ring_iff hemb _).mpr hm)
        rcases chordless_perimeter hemb hpre hxbc h2 with hk | hk
        · exact hA hk
        · exact hB hk
      have hC : Gc.Kernel rc (Gc.node x) := by
        rcases embed_cases hemb hpre x with hc | hc
        · exact absurd hc (by rw [not_or]; exact ⟨hA, hB⟩)
        · exact hc.resolve_right hnotnex
      rw [embed_of_kernel_node hA hB hC, embed_of_kernel hC, hfem, hcubm.node_node_node]

omit [Finite Dm] in
/-- Off the perimeter, a dart outside the kernel whose E-link is also outside
has its N-link in the kernel. -/
private theorem kernel_node_of_not (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {z : Dc} (hzbc : z ∉ rc)
    (hkz : ¬ Gc.Kernel rc z) (hkez : ¬ Gc.Kernel rc (Gc.edge z)) :
    Gc.Kernel rc (Gc.node z) := by
  have hnotnez : ¬ Gc.Kernel rc (Gc.node (Gc.edge z)) := by
    intro hc
    have h1 : Gc.node (Gc.edge z) ∉ rc := not_mem_of_kernel hc
    have h2 : Gc.edge z ∉ rc := fun hm => h1 ((node_mem_ring_iff hemb _).mpr hm)
    rcases chordless_perimeter hemb hpre hzbc h2 with hk | hk
    · exact hkz hk
    · exact hkez hk
  rcases embed_cases hemb hpre z with hc | hc
  · exact absurd hc (by rw [not_or]; exact ⟨hkz, hkez⟩)
  · exact hc.resolve_right hnotnez

/-- **The embedding is injective off the perimeter.**  This is the reference's
`embed_inj`. -/
theorem embed_inj (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x y : Dc} (hxbc : x ∉ rc)
    (hybc : y ∉ rc) (heq : embed Gc Gm rc h x = embed Gc Gm rc h y) : x = y := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have key : ∀ u v : Dc, Gc.Kernel rc u → v ∉ rc →
      embed Gc Gm rc h u = embed Gc Gm rc h v → u = v := by
    intro u v hku hvbc heq'
    rw [embed_of_kernel hku] at heq'
    by_cases hkv : Gc.Kernel rc v
    · rw [embed_of_kernel hkv] at heq'
      exact pre_embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hku
        hkv heq'
    · by_cases hkev : Gc.Kernel rc (Gc.edge v)
      · rw [embed_of_kernel_edge hkv hkev] at heq'
        have h1 : Gc.edge (Gc.edge v) = u :=
          embed_full hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hkev hku
            heq'.symm
        rw [hplainc.edge_edge] at h1
        exact h1.symm
      · have hknv : Gc.Kernel rc (Gc.node v) := kernel_node_of_not hemb hpre hvbc hkv hkev
        rw [embed_of_kernel_node hkv hkev hknv] at heq'
        have hkenu : Gc.Kernel rc (Gc.edge (Gc.node u)) := by
          rw [← kernel_face, Gc.nodeK u]; exact hku
        have h2 : h u = Gm.face (h (Gc.edge (Gc.node u))) := by
          have h3 := hpre.face _ hkenu
          rwa [Gc.nodeK u] at h3
        rw [h2] at heq'
        have h4 : h (Gc.edge (Gc.node u)) = Gm.edge (h (Gc.node v)) := Gm.face.injective heq'
        have h5 : Gc.edge (Gc.node v) = Gc.edge (Gc.node u) :=
          embed_full hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hknv hkenu
            h4.symm
        exact (Gc.node.injective (Gc.edge.injective h5)).symm
  by_cases hkx : Gc.Kernel rc x
  · exact key x y hkx hybc heq
  · by_cases hky : Gc.Kernel rc y
    · exact (key y x hky hxbc heq.symm).symm
    · by_cases hknx : Gc.Kernel rc (Gc.node x)
      · have h2 : Gc.node y ∉ rc := fun hm => hybc ((node_mem_ring_iff hemb y).mp hm)
        have h3 : embed Gc Gm rc h (Gc.node x) = embed Gc Gm rc h (Gc.node y) := by
          rw [embedN hemb hplainm hcubm hpre hxbc, embedN hemb hplainm hcubm hpre hybc, heq]
        exact Gc.node.injective (key _ _ hknx h2 h3)
      · by_cases hkny : Gc.Kernel rc (Gc.node y)
        · have h2 : Gc.node x ∉ rc := fun hm => hxbc ((node_mem_ring_iff hemb x).mp hm)
          have h3 : embed Gc Gm rc h (Gc.node y) = embed Gc Gm rc h (Gc.node x) := by
            rw [embedN hemb hplainm hcubm hpre hybc, embedN hemb hplainm hcubm hpre hxbc,
              heq]
          exact (Gc.node.injective (key _ _ hkny h2 h3)).symm
        · have hkex : Gc.Kernel rc (Gc.edge x) := by
            by_contra hc
            exact hknx (kernel_node_of_not hemb hpre hxbc hkx hc)
          have hkey : Gc.Kernel rc (Gc.edge y) := by
            by_contra hc
            exact hkny (kernel_node_of_not hemb hpre hybc hky hc)
          have h2 : Gc.edge y ∉ rc := not_mem_of_kernel hkey
          have h3 : embed Gc Gm rc h (Gc.edge x) = embed Gc Gm rc h (Gc.edge y) := by
            rw [embedE hemb hplainm hcubm hpre, embedE hemb hplainm hcubm hpre, heq]
          exact Gc.edge.injective (key _ _ hkex h2 h3)

end EmbedMorph

/-! ### The disk map

The darts off the perimeter carry a hypermap of their own: the E-links and
F-links that would leave the complement of `rc` are pushed one step further,
which is exactly the reference's `embed_disk`. -/

section EmbedDisk

open scoped Classical in
/-- The `edge` map of the disk: the E-link of a dart, pushed one N-step further
when it lands on the perimeter. -/
noncomputable def embdEdge (Gc : Hypermap Dc) (rc : List Dc) (x : Dc) : Dc :=
  if Gc.edge x ∈ rc then Gc.edge (Gc.node (Gc.edge x)) else Gc.edge x

open scoped Classical in
/-- The `face` map of the disk: the F-link of a dart, pushed one F-step further
when it lands on the perimeter. -/
noncomputable def embdFace (Gc : Hypermap Dc) (rc : List Dc) (x : Dc) : Dc :=
  if Gc.face x ∈ rc then Gc.face (Gc.face x) else Gc.face x

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- Off the perimeter the disk `edge` is the E-link. -/
theorem embdEdge_of_not_mem {x : Dc} (hx : Gc.edge x ∉ rc) : embdEdge Gc rc x = Gc.edge x := by
  rw [embdEdge, ite_eq_right hx]

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- On the perimeter the disk `edge` takes an extra N-step. -/
theorem embdEdge_of_mem {x : Dc} (hx : Gc.edge x ∈ rc) :
    embdEdge Gc rc x = Gc.edge (Gc.node (Gc.edge x)) := by
  rw [embdEdge, ite_eq_left hx]

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- Off the perimeter the disk `face` is the F-link. -/
theorem embdFace_of_not_mem {x : Dc} (hx : Gc.face x ∉ rc) : embdFace Gc rc x = Gc.face x := by
  rw [embdFace, ite_eq_right hx]

omit [Finite Dc] [Finite Dm] in
open scoped Classical in
/-- On the perimeter the disk `face` takes an extra F-step. -/
theorem embdFace_of_mem {x : Dc} (hx : Gc.face x ∈ rc) :
    embdFace Gc rc x = Gc.face (Gc.face x) := by
  rw [embdFace, ite_eq_left hx]

omit [Finite Dm] in
/-- The disk `edge` stays off the perimeter. -/
theorem embdEdge_not_mem (hemb : Gc.Embeddable rc) {x : Dc} : embdEdge Gc rc x ∉ rc := by
  classical
  by_cases hx : Gc.edge x ∈ rc
  · rw [embdEdge_of_mem hx]
    rcases edge_perimeter hemb (Gc.node (Gc.edge x)) with hc | hc
    · exact absurd ((node_mem_ring_iff hemb (Gc.edge x)).mpr hx) hc
    · exact hc
  · rw [embdEdge_of_not_mem hx]
    exact hx

omit [Finite Dm] in
/-- The disk `face` stays off the perimeter. -/
theorem embdFace_not_mem (hemb : Gc.Embeddable rc) {x : Dc} : embdFace Gc rc x ∉ rc := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  by_cases hx : Gc.face x ∈ rc
  · rw [embdFace_of_mem hx]
    rcases edge_perimeter hemb (Gc.face x) with hc | hc
    · exact absurd hx hc
    · intro hm
      exact hc (by
        rw [← hplainc.node_face (Gc.face x)]
        exact (node_mem_ring_iff hemb _).mpr hm)
  · rw [embdFace_of_not_mem hx]
    exact hx

omit [Finite Dm] in
/-- The triangular identity of the disk map. -/
theorem embd_cancel3 (hemb : Gc.Embeddable rc) {x : Dc} (hx : x ∉ rc) :
    Gc.node (embdFace Gc rc (embdEdge Gc rc x)) = x := by
  classical
  by_cases hex : Gc.edge x ∈ rc
  · have h1 : Gc.face (embdEdge Gc rc x) = Gc.edge x := by
      rw [embdEdge_of_mem hex]
      exact Gc.nodeK (Gc.edge x)
    rw [embdFace_of_mem (by rw [h1]; exact hex), h1]
    exact Gc.edgeK x
  · rw [embdEdge_of_not_mem hex]
    have h2 : Gc.face (Gc.edge x) ∉ rc := by
      intro hm
      exact hx (by
        have := (node_mem_ring_iff hemb (Gc.face (Gc.edge x))).mpr hm
        rwa [Gc.edgeK x] at this)
    rw [embdFace_of_not_mem h2]
    exact Gc.edgeK x

variable (Gc rc)

/-- **The disk map**: the hypermap carried by the darts off the perimeter.
This is the reference's `embed_disk`. -/
noncomputable def embedDisk (hemb : Gc.Embeddable rc) : Hypermap {x : Dc // x ∉ rc} :=
  Hypermap.ofCancel3
    (fun u => ⟨embdEdge Gc rc u.1, embdEdge_not_mem hemb⟩)
    (fun u => ⟨Gc.node u.1, fun hm => u.2 ((node_mem_ring_iff hemb u.1).mp hm)⟩)
    (fun u => ⟨embdFace Gc rc u.1, embdFace_not_mem hemb⟩)
    (fun u => Subtype.ext (embd_cancel3 hemb u.2))

/-- The projection of a disk dart back into `Gc`. -/
def embd (rc : List Dc) (u : {x : Dc // x ∉ rc}) : Dc := u.1

variable {Gc rc}

omit [Finite Dm] in
/-- The `edge` map of the disk map, read in `Gc`. -/
@[simp] theorem embedDisk_edge (hemb : Gc.Embeddable rc) (u : {x : Dc // x ∉ rc}) :
    ((embedDisk Gc rc hemb).edge u).1 = embdEdge Gc rc u.1 := rfl

omit [Finite Dm] in
/-- The `node` map of the disk map, read in `Gc`. -/
@[simp] theorem embedDisk_node (hemb : Gc.Embeddable rc) (u : {x : Dc // x ∉ rc}) :
    ((embedDisk Gc rc hemb).node u).1 = Gc.node u.1 := rfl

omit [Finite Dm] in
/-- The `face` map of the disk map, read in `Gc`. -/
@[simp] theorem embedDisk_face (hemb : Gc.Embeddable rc) (u : {x : Dc // x ∉ rc}) :
    ((embedDisk Gc rc hemb).face u).1 = embdFace Gc rc u.1 := rfl

omit [Finite Dc] [Finite Dm] in
/-- The projection of the disk map is injective. -/
theorem embd_injective : Function.Injective (embd rc) := fun _ _ hxy => Subtype.ext hxy

omit [Finite Dc] [Finite Dm] in
/-- Cyclic chains transfer along a map. -/
private theorem isCyclicChain_map_iff {α β : Type*} (f : α → β) {e' : β → β → Prop}
    {l : List α} :
    IsCyclicChain e' (l.map f) ↔ IsCyclicChain (fun a b => e' (f a) (f b)) l := by
  constructor
  · intro hc
    refine ⟨(List.isChain_map f).mp hc.isChain, fun a ha b hb => ?_⟩
    refine hc.2 (f a) ?_ (f b) ?_
    · rw [Option.mem_def, List.getLast?_map]
      rw [Option.mem_def] at ha
      rw [ha]
      rfl
    · rw [Option.mem_def, List.head?_map]
      rw [Option.mem_def] at hb
      rw [hb]
      rfl
  · intro hc
    refine ⟨(List.isChain_map f).mpr hc.isChain, fun a ha b hb => ?_⟩
    rw [Option.mem_def, List.getLast?_map] at ha
    rw [Option.mem_def, List.head?_map] at hb
    cases hl : l.getLast? with
    | none => rw [hl] at ha; simp at ha
    | some a' =>
      cases hh : l.head? with
      | none => rw [hh] at hb; simp at hb
      | some b' =>
        rw [hl] at ha
        rw [hh] at hb
        simp only [Option.map_some, Option.some.injEq] at ha hb
        subst ha
        subst hb
        exact hc.2 a' (by rw [Option.mem_def, hl]) b' (by rw [Option.mem_def, hh])

variable (Gc rc)

omit [Finite Dm] in
/-- The border of the disk map: the E-image of the perimeter, lifted into the
disk. -/
def embdRing (hemb : Gc.Embeddable rc) : List {x : Dc // x ∉ rc} :=
  rc.pmap (fun z (hz : z ∈ rc) =>
    (⟨Gc.edge z, (edge_perimeter hemb z).resolve_left (not_not_intro hz)⟩ :
      {x : Dc // x ∉ rc})) fun _ hz => hz

variable {Gc rc}

omit [Finite Dm] in
/-- The border of the disk map projects onto the E-image of the perimeter. -/
@[simp] theorem map_embd_ring (hemb : Gc.Embeddable rc) :
    (embdRing Gc rc hemb).map (embd rc) = rc.map Gc.edge := by
  rw [embdRing, List.map_pmap]
  exact List.pmap_eq_map _

omit [Finite Dm] in
/-- **The disk map preserves and reflects faces.**  This is the reference's
`cface_embd`. -/
theorem cface_embd (hemb : Gc.Embeddable rc) {u v : {x : Dc // x ∉ rc}} :
    (embedDisk Gc rc hemb).CFace u v ↔ Gc.CFace u.1 v.1 := by
  classical
  have hstep : ∀ w : {x : Dc // x ∉ rc},
      Gc.CFace w.1 (((embedDisk Gc rc hemb).face w).1) := by
    intro w
    change Gc.CFace w.1 (embdFace Gc rc w.1)
    by_cases hw : Gc.face w.1 ∈ rc
    · rw [embdFace_of_mem hw]
      exact (Gc.cface_face w.1).trans (Gc.cface_face (Gc.face w.1))
    · rw [embdFace_of_not_mem hw]
      exact Gc.cface_face w.1
  constructor
  · intro huv
    obtain ⟨n, hn⟩ := huv.exists_nat_pow_eq
    rw [Perm.coe_pow] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (hstep _)
  · intro huv
    have key : ∀ n m : ℕ, m ≤ n → ∀ (a : Dc) (ha : a ∉ rc) (b : Dc) (hb : b ∉ rc),
        Gc.face^[m] a = b → (embedDisk Gc rc hemb).CFace ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro n
      induction n with
      | zero =>
        intro m hm a ha b hb hab
        rw [Nat.le_zero] at hm
        subst hm
        simp only [Function.iterate_zero, id_eq] at hab
        subst hab
        exact Equiv.Perm.SameCycle.refl _ _
      | succ n ih =>
        intro m hm a ha b hb hab
        rcases m with _ | m'
        · simp only [Function.iterate_zero, id_eq] at hab
          subst hab
          exact Equiv.Perm.SameCycle.refl _ _
        · by_cases hfa : Gc.face a ∈ rc
          · rcases m' with _ | m''
            · exfalso
              have h0 : Gc.face a = b := by simpa using hab
              exact hb (h0 ▸ hfa)
            · have hffa : Gc.face (Gc.face a) ∉ rc := by
                have h0 := embdFace_not_mem (Gc := Gc) (rc := rc) hemb (x := a)
                rwa [embdFace_of_mem hfa] at h0
              have hstep2 : Gc.face^[m''] (Gc.face (Gc.face a)) = b := by
                rw [← hab, Function.iterate_succ_apply, Function.iterate_succ_apply]
              have h1 := ih m'' (by omega) (Gc.face (Gc.face a)) hffa b hb hstep2
              have h2 : (embedDisk Gc rc hemb).face ⟨a, ha⟩
                  = ⟨Gc.face (Gc.face a), hffa⟩ :=
                Subtype.ext (by
                  change embdFace Gc rc a = Gc.face (Gc.face a)
                  exact embdFace_of_mem hfa)
              refine Equiv.Perm.SameCycle.trans ?_ h1
              rw [← h2]
              exact (embedDisk Gc rc hemb).cface_face _
          · have hstep2 : Gc.face^[m'] (Gc.face a) = b := by
              rw [← hab, Function.iterate_succ_apply]
            have h1 := ih m' (by omega) (Gc.face a) hfa b hb hstep2
            have h2 : (embedDisk Gc rc hemb).face ⟨a, ha⟩ = ⟨Gc.face a, hfa⟩ :=
              Subtype.ext (by
                change embdFace Gc rc a = Gc.face a
                exact embdFace_of_not_mem hfa)
            refine Equiv.Perm.SameCycle.trans ?_ h1
            rw [← h2]
            exact (embedDisk Gc rc hemb).cface_face _
    obtain ⟨n, hn⟩ := huv.exists_nat_pow_eq
    rw [Perm.coe_pow] at hn
    have h3 := key n n le_rfl u.1 u.2 v.1 v.2 hn
    simpa using h3

omit [Finite Dm] in
/-- **The border of the disk map is a face-simple E-cycle.**  This is the
reference's `scycle_embd_ring`. -/
theorem scycle_embd_ring (hemb : Gc.Embeddable rc) :
    (embedDisk Gc rc hemb).Scycle
      (fun u v => v = (embedDisk Gc rc hemb).edge u) (embdRing Gc rc hemb) := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  refine ⟨?_, ?_⟩
  · have h1 : IsCyclicChain (fun a b : Dc => b = embdEdge Gc rc a) (rc.map Gc.edge) := by
      refine isCyclicChain_of_rel_getElem ?_
      intro i k hi hk hik
      have hi' : i < rc.length := by simpa using hi
      have hk' : k < rc.length := by simpa using hk
      have hrel : rc[k] = Gc.node rc[i] :=
        rel_getElem_succ hemb.base.base.base.cycle hi' hk' (by simpa using hik)
      have hmi : rc[i] ∈ rc := List.getElem_mem hi'
      simp only [List.getElem_map]
      rw [embdEdge_of_mem (by rw [hplainc.edge_edge]; exact hmi), hplainc.edge_edge, hrel]
    have h2 : IsCyclicChain (fun a b : Dc => b = embdEdge Gc rc a)
        ((embdRing Gc rc hemb).map (embd rc)) := by
      rw [map_embd_ring]; exact h1
    exact ((isCyclicChain_map_iff (embd rc)).mp h2).congr fun _ _ huv => Subtype.ext huv
  · have h4 : Gc.Simple ((embdRing Gc rc hemb).map (embd rc)) := by
      rw [map_embd_ring]; exact (scycle_edge_ring hemb).simple
    have h5 : (embdRing Gc rc hemb).Pairwise
        (fun u v => ¬ Gc.CFace (embd rc u) (embd rc v)) := List.pairwise_map.mp h4
    exact h5.imp fun {u v} hc hd => hc ((cface_embd hemb).mp hd)

/-- A permutation cycle is closed under the permutation in both directions. -/
private theorem mem_isCyclicChain_iff {D : Type*} [Finite D] {f : Equiv.Perm D} {r : List D}
    (hnd : r.Nodup) (hc : IsCyclicChain (fun u v => v = f u) r) (x : D) :
    f x ∈ r ↔ x ∈ r := by
  classical
  have hsub : (r.map f).toFinset ⊆ r.toFinset := by
    intro a ha
    rw [List.mem_toFinset] at ha ⊢
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact mem_of_isCyclicChain hc hb
  have hcard : r.toFinset.card ≤ (r.map f).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd,
      List.toFinset_card_of_nodup (hnd.map f.injective), List.length_map]
  have heq : (r.map f).toFinset = r.toFinset := Finset.eq_of_subset_of_card_le hsub hcard
  constructor
  · intro hx
    have h1 : f x ∈ (r.map f).toFinset := by rw [heq, List.mem_toFinset]; exact hx
    rw [List.mem_toFinset] at h1
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp h1
    rwa [f.injective hbx] at hb
  · intro hx
    exact mem_of_isCyclicChain hc hx

variable (Gc Gm rc)

/-- The projection of a disk dart into the target hypermap. -/
noncomputable def embdd (hh : Dc → Dm) (u : {x : Dc // x ∉ rc}) : Dm :=
  embed Gc Gm rc hh u.1

variable {Gc Gm rc}

/-- The border of the disk map is closed under the disk `edge`, in both
directions. -/
theorem mem_embd_ring_edge_iff (hemb : Gc.Embeddable rc) (u : {x : Dc // x ∉ rc}) :
    (embedDisk Gc rc hemb).edge u ∈ embdRing Gc rc hemb ↔ u ∈ embdRing Gc rc hemb :=
  mem_isCyclicChain_iff (scycle_embd_ring hemb).nodup (scycle_embd_ring hemb).isCyclicChain u

omit [Finite Dm] in
/-- A disk dart is on the border exactly when it is on the E-image of the
perimeter. -/
theorem mem_embd_ring_iff (hemb : Gc.Embeddable rc) {u : {x : Dc // x ∉ rc}} :
    u ∈ embdRing Gc rc hemb ↔ u.1 ∈ rc.map Gc.edge := by
  constructor
  · intro hu
    rw [← map_embd_ring hemb]
    exact List.mem_map.mpr ⟨u, hu, rfl⟩
  · intro hu
    rw [← map_embd_ring hemb] at hu
    obtain ⟨v, hv, hvu⟩ := List.mem_map.mp hu
    rwa [embd_injective hvu] at hv

/-- **The disk projection into the target is injective.**  This is the
reference's `embdd_inj`. -/
theorem embdd_inj (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) :
    Function.Injective (embdd Gc Gm rc h) := by
  intro u v huv
  exact Subtype.ext (embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
    u.2 v.2 huv)

omit [Finite Dm] in
/-- **The disk projection commutes with `edge` off the border.**  This is the
reference's `embddE`. -/
theorem embddE (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {u : {x : Dc // x ∉ rc}}
    (hu : u ∉ embdRing Gc rc hemb) :
    embdd Gc Gm rc h ((embedDisk Gc rc hemb).edge u) = Gm.edge (embdd Gc Gm rc h u) := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hnm : u.1 ∉ rc.map Gc.edge := fun hc => hu ((mem_embd_ring_iff hemb).mpr hc)
  have heu : Gc.edge u.1 ∉ rc := by
    intro hc
    exact hnm (List.mem_map.mpr ⟨Gc.edge u.1, hc, hplainc.edge_edge u.1⟩)
  change embed Gc Gm rc h (embdEdge Gc rc u.1) = Gm.edge (embed Gc Gm rc h u.1)
  rw [embdEdge_of_not_mem heu]
  exact embedE hemb hplainm hcubm hpre u.1

omit [Finite Dm] in
/-- **The disk projection commutes with `node`.**  This is the reference's
`embddN`. -/
theorem embddN (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (u : {x : Dc // x ∉ rc}) :
    embdd Gc Gm rc h ((embedDisk Gc rc hemb).node u) = Gm.node (embdd Gc Gm rc h u) :=
  embedN hemb hplainm hcubm hpre u.2

end EmbedDisk

/-! ### The remainder map

The darts of the target that the interior of the disk map does not already
account for carry a hypermap of their own, glued to the disk map along the image
of the disk border.  This is the reference's `embed_rem`. -/

section EmbedRem

variable (Gc Gm rc)

/-- The darts of the target covered by the interior of the disk map. -/
def embdInner (hh : Dc → Dm) (hemb : Gc.Embeddable rc) : Set Dm :=
  {x | ∃ u : {y : Dc // y ∉ rc}, u ∉ embdRing Gc rc hemb ∧ embdd Gc Gm rc hh u = x}

open scoped Classical in
/-- The `node` map of the remainder map: on the image of the disk border it
follows the disk, and elsewhere it is the target's `node`. -/
noncomputable def embrNode (hh : Dc → Dm) (hemb : Gc.Embeddable rc) (x : Dm) : Dm :=
  if hx : ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc hh u = x then
    embdd Gc Gm rc hh ((embedDisk Gc rc hemb).node ((embedDisk Gc rc hemb).face hx.choose))
  else Gm.node x

open scoped Classical in
/-- The `face` map of the remainder map: on the E-image of the disk border it
follows the disk, and elsewhere it is the target's `face`. -/
noncomputable def embrFace (hh : Dc → Dm) (hemb : Gc.Embeddable rc) (x : Dm) : Dm :=
  if hx : ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc hh u = Gm.edge x then
    embdd Gc Gm rc hh ((embedDisk Gc rc hemb).edge hx.choose)
  else Gm.face x

variable {Gc Gm rc}

omit [Finite Dm] in
/-- Away from the image of the disk border the remainder `node` is the target's
`node`. -/
theorem embrNode_of_not_mem (hemb : Gc.Embeddable rc) {x : Dm}
    (hx : ¬ ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = x) :
    embrNode Gc Gm rc h hemb x = Gm.node x := by
  rw [embrNode, dite_eq_right hx]

omit [Finite Dm] in
/-- On the image of the disk border the remainder `node` follows the disk. -/
theorem embrNode_of_mem (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) {u : {y : Dc // y ∉ rc}}
    (hu : u ∈ embdRing Gc rc hemb) :
    embrNode Gc Gm rc h hemb (embdd Gc Gm rc h u)
      = embdd Gc Gm rc h ((embedDisk Gc rc hemb).node ((embedDisk Gc rc hemb).face u)) := by
  have hx : ∃ v ∈ embdRing Gc rc hemb, embdd Gc Gm rc h v = embdd Gc Gm rc h u := ⟨u, hu, rfl⟩
  rw [embrNode, dite_eq_left hx, hinj hx.choose_spec.2]

omit [Finite Dm] in
/-- Away from the E-image of the disk border the remainder `face` is the
target's `face`. -/
theorem embrFace_of_not_mem (hemb : Gc.Embeddable rc) {x : Dm}
    (hx : ¬ ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = Gm.edge x) :
    embrFace Gc Gm rc h hemb x = Gm.face x := by
  rw [embrFace, dite_eq_right hx]

omit [Finite Dm] in
/-- On the E-image of the disk border the remainder `face` follows the disk. -/
theorem embrFace_of_mem (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) {u : {y : Dc // y ∉ rc}} {x : Dm}
    (hu : u ∈ embdRing Gc rc hemb) (hux : embdd Gc Gm rc h u = Gm.edge x) :
    embrFace Gc Gm rc h hemb x = embdd Gc Gm rc h ((embedDisk Gc rc hemb).edge u) := by
  have hx : ∃ v ∈ embdRing Gc rc hemb, embdd Gc Gm rc h v = Gm.edge x := ⟨u, hu, hux⟩
  rw [embrFace, dite_eq_left hx, hinj (hx.choose_spec.2.trans hux.symm)]

omit [Finite Dm] in
/-- A dart of the disk border has its image outside the interior. -/
theorem embdd_mem_ring_not_mem_inner (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) {u : {y : Dc // y ∉ rc}}
    (hu : u ∈ embdRing Gc rc hemb) :
    embdd Gc Gm rc h u ∉ embdInner Gc Gm rc h hemb := by
  rintro ⟨v, hv, hvu⟩
  exact hv (hinj hvu ▸ hu)

omit [Finite Dm] in
/-- The E-link of a dart outside the interior stays outside. -/
theorem embrEdge_not_mem_inner (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x : Dm}
    (hx : x ∉ embdInner Gc Gm rc h hemb) :
    Gm.edge x ∉ embdInner Gc Gm rc h hemb := by
  rintro ⟨u, hu, hux⟩
  refine hx ⟨(embedDisk Gc rc hemb).edge u, ?_, ?_⟩
  · rw [mem_embd_ring_edge_iff]
    exact hu
  · rw [embddE hemb hplainm hcubm hpre hu, hux, hplainm.edge_edge]

omit [Finite Dm] in
/-- The remainder `node` of a dart outside the interior stays outside. -/
theorem embrNode_not_mem_inner (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {x : Dm}
    (hx : x ∉ embdInner Gc Gm rc h hemb) :
    embrNode Gc Gm rc h hemb x ∉ embdInner Gc Gm rc h hemb := by
  classical
  by_cases hc : ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = x
  · obtain ⟨u, hu, hux⟩ := hc
    rw [← hux, embrNode_of_mem hemb hinj hu]
    refine embdd_mem_ring_not_mem_inner hemb hinj ?_
    rw [← mem_embd_ring_edge_iff hemb, (embedDisk Gc rc hemb).faceK u]
    exact hu
  · rw [embrNode_of_not_mem hemb hc]
    rintro ⟨u, hu, hux⟩
    have h1 : Gm.node (Gm.node (embdd Gc Gm rc h u)) = x := by
      rw [hux, hcubm.node_node_node]
    have h2 : embdd Gc Gm rc h ((embedDisk Gc rc hemb).node
        ((embedDisk Gc rc hemb).node u)) = x := by
      rw [embddN hemb hplainm hcubm hpre, embddN hemb hplainm hcubm hpre]
      exact h1
    by_cases hnu : (embedDisk Gc rc hemb).node ((embedDisk Gc rc hemb).node u)
        ∈ embdRing Gc rc hemb
    · exact hc ⟨_, hnu, h2⟩
    · exact hx ⟨_, hnu, h2⟩

omit [Finite Dm] in
/-- The remainder `face` of a dart outside the interior stays outside. -/
theorem embrFace_not_mem_inner (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {x : Dm}
    (hx : x ∉ embdInner Gc Gm rc h hemb) :
    embrFace Gc Gm rc h hemb x ∉ embdInner Gc Gm rc h hemb := by
  classical
  by_cases hc : ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = Gm.edge x
  · obtain ⟨u, hu, hux⟩ := hc
    rw [embrFace_of_mem hemb hinj hu hux]
    refine embdd_mem_ring_not_mem_inner hemb hinj ?_
    rw [mem_embd_ring_edge_iff]
    exact hu
  · rw [embrFace_of_not_mem hemb hc]
    rintro ⟨u, hu, hux⟩
    have h1 : embdd Gc Gm rc h ((embedDisk Gc rc hemb).node u) = Gm.edge x := by
      rw [embddN hemb hplainm hcubm hpre, hux, hplainm.node_face]
    by_cases hnu : (embedDisk Gc rc hemb).node u ∈ embdRing Gc rc hemb
    · exact hc ⟨_, hnu, h1⟩
    · exact embrEdge_not_mem_inner hemb hplainm hcubm hpre hx ⟨_, hnu, h1⟩

omit [Finite Dm] in
/-- The triangular identity of the remainder map. -/
theorem embr_cancel3 (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {x : Dm}
    (hx : x ∉ embdInner Gc Gm rc h hemb) :
    embrNode Gc Gm rc h hemb (embrFace Gc Gm rc h hemb (Gm.edge x)) = x := by
  classical
  by_cases hc : ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = x
  · obtain ⟨u, hu, hux⟩ := hc
    have heu : (embedDisk Gc rc hemb).edge u ∈ embdRing Gc rc hemb := by
      rw [mem_embd_ring_edge_iff]; exact hu
    rw [embrFace_of_mem hemb hinj hu (by rw [hplainm.edge_edge]; exact hux),
      embrNode_of_mem hemb hinj heu, (embedDisk Gc rc hemb).edgeK u]
    exact hux
  · have hc' : ¬ ∃ u ∈ embdRing Gc rc hemb,
        embdd Gc Gm rc h u = Gm.edge (Gm.edge x) := by
      rw [hplainm.edge_edge]; exact hc
    rw [embrFace_of_not_mem hemb hc']
    by_cases hd : ∃ v ∈ embdRing Gc rc hemb,
        embdd Gc Gm rc h v = Gm.face (Gm.edge x)
    · exfalso
      obtain ⟨v, hv, hvx⟩ := hd
      have h1 : embdd Gc Gm rc h ((embedDisk Gc rc hemb).node v) = x := by
        rw [embddN hemb hplainm hcubm hpre, hvx, Gm.edgeK]
      by_cases hnv : (embedDisk Gc rc hemb).node v ∈ embdRing Gc rc hemb
      · exact hc ⟨_, hnv, h1⟩
      · exact hx ⟨_, hnv, h1⟩
    · rw [embrNode_of_not_mem hemb hd, Gm.edgeK]

variable (Gc Gm rc)

/-- **The remainder map**: the hypermap carried by the darts of the target
outside the interior of the disk map.  This is the reference's `embed_rem`. -/
noncomputable def embedRem (hh : Dc → Dm) (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm hh {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc hh)) :
    Hypermap {x : Dm // x ∉ embdInner Gc Gm rc hh hemb} :=
  Hypermap.ofCancel3
    (fun w => ⟨Gm.edge w.1, embrEdge_not_mem_inner hemb hplainm hcubm hpre w.2⟩)
    (fun w => ⟨embrNode Gc Gm rc hh hemb w.1,
      embrNode_not_mem_inner hemb hplainm hcubm hpre hinj w.2⟩)
    (fun w => ⟨embrFace Gc Gm rc hh hemb w.1,
      embrFace_not_mem_inner hemb hplainm hcubm hpre hinj w.2⟩)
    (fun w => Subtype.ext (embr_cancel3 hemb hplainm hcubm hpre hinj w.2))

/-- The projection of a remainder dart back into the target. -/
def embr (hh : Dc → Dm) (hemb : Gc.Embeddable rc) :
    {x : Dm // x ∉ embdInner Gc Gm rc hh hemb} → Dm := fun w => w.1

variable {Gc Gm rc}

omit [Finite Dm] in
/-- The projection of the remainder map is injective. -/
theorem embr_injective (hemb : Gc.Embeddable rc) :
    Function.Injective (embr Gc Gm rc h hemb) := fun _ _ hxy => Subtype.ext hxy

variable (Gc Gm rc)

/-- The border of the remainder map: the image of the disk border, reversed. -/
noncomputable def embrRing (hh : Dc → Dm) (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc hh)) :
    List {x : Dm // x ∉ embdInner Gc Gm rc hh hemb} :=
  (embdRing Gc rc hemb).reverse.pmap
    (fun u (hu : u ∈ (embdRing Gc rc hemb).reverse) =>
      (⟨embdd Gc Gm rc hh u,
        embdd_mem_ring_not_mem_inner hemb hinj (List.mem_reverse.mp hu)⟩ :
        {x : Dm // x ∉ embdInner Gc Gm rc hh hemb}))
    fun _ hu => hu

variable {Gc Gm rc}

omit [Finite Dm] in
/-- The border of the remainder map projects onto the reversed image of the
disk border. -/
@[simp] theorem map_embr_ring (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embrRing Gc Gm rc h hemb hinj).map (embr Gc Gm rc h hemb)
      = ((embdRing Gc rc hemb).map (embdd Gc Gm rc h)).reverse := by
  rw [embrRing, List.map_pmap, ← List.map_reverse]
  exact List.pmap_eq_map _

omit [Finite Dm] in
/-- A remainder dart is on the border exactly when it is the image of a dart of
the disk border. -/
theorem mem_embr_ring_iff (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h))
    {w : {x : Dm // x ∉ embdInner Gc Gm rc h hemb}} :
    w ∈ embrRing Gc Gm rc h hemb hinj ↔
      ∃ u ∈ embdRing Gc rc hemb, embdd Gc Gm rc h u = w.1 := by
  constructor
  · intro hw
    have h1 : w.1 ∈ ((embdRing Gc rc hemb).map (embdd Gc Gm rc h)).reverse := by
      rw [← map_embr_ring hemb hinj]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [List.mem_reverse] at h1
    obtain ⟨u, hu, huw⟩ := List.mem_map.mp h1
    exact ⟨u, hu, huw⟩
  · rintro ⟨u, hu, huw⟩
    have h1 : w.1 ∈ ((embdRing Gc rc hemb).map (embdd Gc Gm rc h)).reverse := by
      rw [List.mem_reverse]
      exact List.mem_map.mpr ⟨u, hu, huw⟩
    rw [← map_embr_ring hemb hinj] at h1
    obtain ⟨v, hv, hvw⟩ := List.mem_map.mp h1
    rwa [embr_injective hemb hvw] at hv

omit [Finite Dm] in
/-- The border of the remainder map has no repetitions. -/
theorem nodup_embr_ring (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embrRing Gc Gm rc h hemb hinj).Nodup := by
  have h1 : ((embrRing Gc Gm rc h hemb hinj).map (embr Gc Gm rc h hemb)).Nodup := by
    rw [map_embr_ring hemb hinj, List.nodup_reverse]
    exact (scycle_embd_ring hemb).nodup.map hinj
  exact h1.of_map _

/-- **The border of the remainder map is an N-cycle.**  This is the reference's
`ucycle_embr_ring`. -/
theorem cycle_embr_ring (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    IsCyclicChain
      (fun w w' => w' = (embedRem Gc Gm rc h hemb hplainm hcubm hpre hinj).node w)
      (embrRing Gc Gm rc h hemb hinj) := by
  classical
  have hrev : IsCyclicChain (fun u v => u = (embedDisk Gc rc hemb).edge v)
      (embdRing Gc rc hemb).reverse := (scycle_embd_ring hemb).isCyclicChain.reverse
  have hkey : IsCyclicChain
      (fun u v => embdd Gc Gm rc h v = embrNode Gc Gm rc h hemb (embdd Gc Gm rc h u))
      (embdRing Gc rc hemb).reverse := by
    refine isCyclicChain_of_rel_getElem ?_
    intro i k hi hk hik
    have h1 := rel_getElem_succ hrev hi hk hik
    have hmem : (embdRing Gc rc hemb).reverse[i] ∈ embdRing Gc rc hemb := by
      rw [← List.mem_reverse]
      exact List.getElem_mem hi
    rw [embrNode_of_mem hemb hinj hmem, h1, (embedDisk Gc rc hemb).edgeK]
  have h2 : IsCyclicChain
      (fun w w' => embr Gc Gm rc h hemb w'
        = embrNode Gc Gm rc h hemb (embr Gc Gm rc h hemb w))
      (embrRing Gc Gm rc h hemb hinj) := by
    refine (isCyclicChain_map_iff (embr Gc Gm rc h hemb)
      (e' := fun a b : Dm => b = embrNode Gc Gm rc h hemb a)).mp ?_
    rw [map_embr_ring hemb hinj, ← List.map_reverse]
    exact (isCyclicChain_map_iff (embdd Gc Gm rc h)).mpr hkey
  exact h2.congr fun w w' hww => Subtype.ext hww

/-- **The disk map and the remainder map patch the target.**  This is the
reference's `embed_patch`. -/
theorem embed_patch (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    Patch Gm (embedDisk Gc rc hemb) (embedRem Gc Gm rc h hemb hplainm hcubm hpre hinj)
      (embdd Gc Gm rc h) (embr Gc Gm rc h hemb) (embdRing Gc rc hemb)
      (embrRing Gc Gm rc h hemb hinj) where
  injd := hinj
  injr := embr_injective hemb
  scycle_d := scycle_embd_ring hemb
  cycle_r := cycle_embr_ring hemb hplainm hcubm hpre hinj
  nodup_r := nodup_embr_ring hemb hinj
  ring := map_embr_ring hemb hinj
  range_r := by
    intro x
    constructor
    · rintro ⟨w, rfl⟩
      by_cases hc : ∃ u, embdd Gc Gm rc h u = w.1
      · obtain ⟨u, hu⟩ := hc
        refine Or.inr ?_
        by_cases hur : u ∈ embdRing Gc rc hemb
        · exact List.mem_map.mpr ⟨u, hur, hu⟩
        · exact absurd ⟨u, hur, hu⟩ w.2
      · exact Or.inl fun ⟨u, hu⟩ => hc ⟨u, hu⟩
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rintro ⟨u, hu, hux⟩
      rcases hx with hx | hx
      · exact hx ⟨u, hux⟩
      · obtain ⟨v, hv, hvx⟩ := List.mem_map.mp hx
        exact hu (hinj (hux.trans hvx.symm) ▸ hv)
  edge_d := fun _ hu => embddE hemb hplainm hcubm hpre hu
  node_d := embddN hemb hplainm hcubm hpre
  edge_r := fun _ => rfl
  node_r := by
    intro w hw
    change embrNode Gc Gm rc h hemb w.1 = Gm.node w.1
    refine embrNode_of_not_mem hemb fun hc => hw ?_
    exact (mem_embr_ring_iff hemb hinj).mpr hc

end EmbedRem

/-! ### The remainder map is a reducible configuration ring

The remainder map inherits planarity, plainness and cubicity from the target,
and the image of the contract is a valid contract for it. -/

section EmbedContract

/-- **The remainder map is planar.**  This is the reference's `planar_embr`. -/
theorem planar_embr (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embedRem Gc Gm rc h hemb hplainm hcubm hpre hinj).Planar :=
  ((embed_patch hemb hplainm hcubm hpre hinj).planar_patch.mp hplanm).2

/-- **The remainder map is plain.**  This is the reference's `plain_embr`. -/
theorem plain_embr (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embedRem Gc Gm rc h hemb hplainm hcubm hpre hinj).Plain :=
  ((embed_patch hemb hplainm hcubm hpre hinj).plain_patch.mp hplainm).2

/-- **The remainder map is cubic off its border.**  This is the reference's
`cubic_embr`. -/
theorem cubic_embr (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embedRem Gc Gm rc h hemb hplainm hcubm hpre hinj).Quasicubic
      (embrRing Gc Gm rc h hemb hinj) :=
  ((embed_patch hemb hplainm hcubm hpre hinj).cubic_patch.mp hcubm).2

omit [Finite Dm] in
/-- The embedding commutes with the edge closure of a list. -/
theorem insertE_map_embed (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) (p : List Dc) :
    Gm.insertE (p.map (embed Gc Gm rc h)) = (Gc.insertE p).map (embed Gc Gm rc h) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [List.map_cons, insertE, ih, embedE hemb hplainm hcubm hpre x]

/-- The embedding reflects node orbits off the perimeter. -/
theorem cnode_of_embed (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x y : Dc} (hx : x ∉ rc)
    (hy : y ∉ rc) (hcn : Gm.CNode (embed Gc Gm rc h x) (embed Gc Gm rc h y)) :
    Gc.CNode x y := by
  obtain ⟨n, hn⟩ := hcn.exists_nat_pow_eq
  rw [Perm.coe_pow] at hn
  have h1 : ∀ m : ℕ, Gc.node^[m] x ∉ rc := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact fun hc => ih ((node_mem_ring_iff hemb _).mp hc)
  have h2 : ∀ m : ℕ,
      Gm.node^[m] (embed Gc Gm rc h x) = embed Gc Gm rc h (Gc.node^[m] x) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        ← embedN hemb hplainm hcubm hpre (h1 m)]
  rw [h2 n] at hn
  have h3 : Gc.node^[n] x = y :=
    embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre (h1 n) hy hn
  exact ⟨(n : ℤ), by rw [zpow_natCast, Perm.coe_pow]; exact h3⟩

/-- **The image of the contract is node-simple.**  This is the reference's
`embed_sparse`. -/
theorem embed_sparse (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {cc : List Dc}
    (hvc : Gc.ValidContract rc cc) :
    Gm.Sparse (Gm.insertE (cc.map (embed Gc Gm rc h))) := by
  rw [insertE_map_embed hemb hplainm hcubm hpre]
  refine List.pairwise_map.mpr (hvc.sparse.imp_of_mem ?_)
  intro x y hx hy hxy hcn
  exact hxy (cnode_of_embed hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
    (hvc.off_ring x hx) (hvc.off_ring y hy) hcn)

variable (Gc Gm rc)

/-- The ring traces on the border of the remainder map, rotated as in the
reference's `embed_cotrace`. -/
noncomputable def embedCotrace (hh : Dc → Dm) (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm hh {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc hh)) : List Color → Prop :=
  (embedRem Gc Gm rc hh hemb hplainm hcubm hpre hinj).RingTrace
    ((embrRing Gc Gm rc hh hemb hinj).rotate
      ((embrRing Gc Gm rc hh hemb hinj).length - 1))

variable {Gc Gm rc}

/-- **The cotrace of the remainder map is Kempe-closed.**  This is the
reference's `embed_closure`. -/
theorem embed_closure (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    KempeClosed (embedCotrace Gc Gm rc h hemb hplainm hcubm hpre hinj) := by
  classical
  have : Fintype {x : Dm // x ∉ embdInner Gc Gm rc h hemb} := Fintype.ofFinite _
  refine Kempe_map _ _ ⟨⟨⟨plain_embr hemb hplainm hcubm hpre hinj,
    (cubic_embr hemb hplainm hcubm hpre hinj).rotate _⟩, ?_, ?_⟩,
    planar_embr hemb hplanm hplainm hcubm hpre hinj⟩
  · exact isCyclicChain_rotate.mpr (cycle_embr_ring hemb hplainm hcubm hpre hinj)
  · exact List.nodup_rotate.mpr (nodup_embr_ring hemb hinj)

/-- A dart of the perimeter has its F-successor off the perimeter. -/
private theorem face_not_mem_ring (hemb : Gc.Embeddable rc) {c : Dc} (hc : c ∈ rc) :
    Gc.face c ∉ rc := by
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  intro hfc
  rcases edge_perimeter hemb c with h1 | h1
  · exact h1 hc
  · exact h1 (by rw [← hplainc.node_face c]; exact (node_mem_ring_iff hemb _).mpr hfc)

omit [Finite Dm] in
/-- On the perimeter the embedding jumps to the F-successor. -/
private theorem cface_embed_ring (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {c : Dc}
    (hc : c ∈ rc) :
    Gm.CFace (embed Gc Gm rc h c) (embed Gc Gm rc h (Gc.face c)) := by
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hfc : Gc.face c ∉ rc := face_not_mem_ring hemb hc
  have h1 : embed Gc Gm rc h c = Gm.edge (Gm.node (embed Gc Gm rc h (Gc.face c))) := by
    conv_lhs => rw [← Gc.faceK c]
    rw [embedE hemb hplainm hcubm hpre, embedN hemb hplainm hcubm hpre hfc]
  rw [h1]
  have h2 := Gm.cface_face (Gm.edge (Gm.node (embed Gc Gm rc h (Gc.face c))))
  rwa [Gm.nodeK] at h2

/-- **The embedding maps faces into faces.**  This is the reference's
`cface_h1`. -/
theorem cface_embed (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {a b : Dc} (hab : Gc.CFace a b) :
    Gm.CFace (embed Gc Gm rc h a) (embed Gc Gm rc h b) := by
  classical
  have main : ∀ u v : Dc, u ∉ rc → v ∉ rc → Gc.CFace u v →
      Gm.CFace (embed Gc Gm rc h u) (embed Gc Gm rc h v) := by
    intro u v hu hv huv
    exact (embed_patch hemb hplainm hcubm hpre hinj).cface_of_cface_d
      ((cface_embd hemb (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)).mpr huv)
  by_cases hb : b ∈ rc
  · have hfb := face_not_mem_ring hemb hb
    have h1 : Gc.CFace a (Gc.face b) := hab.trans (Gc.cface_face b)
    have h2 : Gm.CFace (embed Gc Gm rc h a) (embed Gc Gm rc h (Gc.face b)) := by
      by_cases ha : a ∈ rc
      · exact (cface_embed_ring hemb hplainm hcubm hpre ha).trans
          (main (Gc.face a) (Gc.face b) (face_not_mem_ring hemb ha) hfb
            ((Gc.cface_face a).symm.trans h1))
      · exact main a (Gc.face b) ha hfb h1
    exact h2.trans (cface_embed_ring hemb hplainm hcubm hpre hb).symm
  · by_cases ha : a ∈ rc
    · exact (cface_embed_ring hemb hplainm hcubm hpre ha).trans
        (main (Gc.face a) b (face_not_mem_ring hemb ha) hb
          ((Gc.cface_face a).symm.trans hab))
    · exact main a b ha hb hab

/-- **The embedding reflects faces out of the kernel.**  This is the reference's
`cface_ac_h1`. -/
theorem cface_embed_iff (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {x w : Dc} (hkx : Gc.Kernel rc x)
    (hw : w ∉ rc) :
    Gm.CFace (embed Gc Gm rc h x) (embed Gc Gm rc h w) ↔ Gc.CFace x w := by
  constructor
  · intro hcf
    rw [embed_of_kernel hkx] at hcf
    obtain ⟨z, hxz, hz⟩ := exists_cface_h hpre hkx hcf
    have hkz : Gc.Kernel rc z := (Kernel.congr hxz).mp hkx
    have h1 : embed Gc Gm rc h z = embed Gc Gm rc h w := by
      rw [embed_of_kernel hkz]; exact hz
    have h2 : z = w := embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
      (not_mem_of_kernel hkz) hw h1
    rw [← h2]
    exact hxz
  · intro hcf
    exact cface_embed hemb hplainm hcubm hpre hinj hcf

omit [Finite Dm] in
/-- The edge closure of a list is closed under `edge`. -/
private theorem edge_mem_insertE (hplainc : Gc.Plain) {p : List Dc} {z : Dc}
    (hz : z ∈ Gc.insertE p) : Gc.edge z ∈ Gc.insertE p := by
  obtain ⟨w, hw, hzw⟩ := (mem_insertE hplainc).mp hz
  exact (mem_insertE hplainc).mpr ⟨w, hw, sameCycle_apply_left.mpr hzw⟩

/-- **The image of the contract is a valid contract for the remainder map.**
This is the reference's `embed_valid_contract`. -/
theorem embed_valid_contract (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar)
    (hplainm : Gm.Plain) (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected)
    (hcubm : Gm.Cubic) (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {cc : List Dc}
    (hvc : Gc.ValidContract rc cc) :
    Gm.ValidContract [] (cc.map (embed Gc Gm rc h)) where
  off_ring := fun _ _ => by simp
  sparse := embed_sparse hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hvc
  one_le_size := by rw [List.length_map]; exact hvc.one_le_size
  size_le := by rw [List.length_map]; exact hvc.size_le
  triad := by
    classical
    intro h4
    rw [List.length_map] at h4
    have hplainc : Gc.Plain := hemb.base.base.base.base.plain
    have hqc : Gc.Quasicubic rc := hemb.base.base.base.base.quasicubic
    obtain ⟨x, hkx, htri⟩ := hvc.triad h4
    have hmapinsert : Gm.insertE (cc.map (embed Gc Gm rc h))
        = (Gc.insertE cc).map (embed Gc Gm rc h) :=
      insertE_map_embed hemb hplainm hcubm hpre cc
    refine ⟨embed Gc Gm rc h x, fband_nil _, ?_, ?_⟩
    · -- three faces around the image of `x` meet the image contract
      have hsub : (embed Gc Gm rc h) '' (Gc.triadSet (Gc.insertE cc) x)
          ⊆ Gm.triadSet (Gm.insertE (cc.map (embed Gc Gm rc h)))
            (embed Gc Gm rc h x) := by
        rintro w ⟨z, ⟨hxz, hfb⟩, rfl⟩
        refine ⟨cface_embed hemb hplainm hcubm hpre hinj hxz, ?_⟩
        obtain ⟨y, hy, hzy⟩ := hfb
        refine ⟨embed Gc Gm rc h y, ?_, ?_⟩
        · rw [hmapinsert]
          exact List.mem_map.mpr ⟨y, hy, rfl⟩
        · rw [← embedE hemb hplainm hcubm hpre z]
          exact cface_embed hemb hplainm hcubm hpre hinj hzy
      have hinjOn : Set.InjOn (embed Gc Gm rc h) (Gc.triadSet (Gc.insertE cc) x) := by
        intro z hz z' hz' heq
        exact embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
          (not_mem_of_kernel ((Kernel.congr hz.1).mp hkx))
          (not_mem_of_kernel ((Kernel.congr hz'.1).mp hkx)) heq
      have h1 := Set.InjOn.ncard_image hinjOn
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 := htri.three_le
      omega
    · -- some dart of the image contract is not adjacent to the image of `x`
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, hny⟩ := htri.not_adj
      have hey : Gc.edge y ∈ Gc.insertE cc := edge_mem_insertE hplainc hy
      have hybc : y ∉ rc := hvc.off_ring y hy
      have heybc : Gc.edge y ∉ rc := hvc.off_ring _ hey
      have hmy : embed Gc Gm rc h y ∈ Gm.insertE (cc.map (embed Gc Gm rc h)) := by
        rw [hmapinsert]; exact List.mem_map.mpr ⟨y, hy, rfl⟩
      have hmey : embed Gc Gm rc h (Gc.edge y) ∈ Gm.insertE (cc.map (embed Gc Gm rc h)) := by
        rw [hmapinsert]; exact List.mem_map.mpr ⟨_, hey, rfl⟩
      have hadj1 : Gm.Adj (embed Gc Gm rc h x) (embed Gc Gm rc h y) := hcon _ hmy
      have hadj2 : Gm.Adj (embed Gc Gm rc h x) (Gm.edge (embed Gc Gm rc h y)) := by
        rw [← embedE hemb hplainm hcubm hpre y]
        exact hcon _ hmey
      refine hny ?_
      rcases adj11_edge hplanm hplainm hbridgem hcubm hBm hadj1 hadj2 with hres | hres
      · have h5 : Gm.CFace (embed Gc Gm rc h x) (Gm.node (embed Gc Gm rc h y)) :=
          mem_spokeRing.mp hres
        rw [← embedN hemb hplainm hcubm hpre hybc,
          cface_embed_iff hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hinj
            hkx (fun hm => hybc ((node_mem_ring_iff hemb y).mp hm))] at h5
        refine ⟨Gc.node y, h5, ?_⟩
        have h6 := Gc.cface_face (Gc.edge (Gc.node y))
        rwa [Gc.nodeK y] at h6
      · have h5 : Gm.CFace (embed Gc Gm rc h x) (Gm.node (Gm.edge (embed Gc Gm rc h y))) :=
          mem_spokeRing.mp hres
        rw [← embedE hemb hplainm hcubm hpre y,
          ← embedN hemb hplainm hcubm hpre heybc,
          cface_embed_iff hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hinj
            hkx (fun hm => heybc ((node_mem_ring_iff hemb (Gc.edge y)).mp hm))] at h5
        -- the face of `y` is off the perimeter, and `face y = node (node (edge y))`
        have hnfy : Gc.node (Gc.face y) = Gc.edge y := hplainc.node_face y
        have hfybc : Gc.face y ∉ rc := by
          intro hm
          exact heybc (by rw [← hnfy]; exact (node_mem_ring_iff hemb _).mpr hm)
        have hn3 : Gc.node (Gc.node (Gc.node (Gc.edge y))) = Gc.edge y :=
          hqc.node_node_node heybc
        have hfy : Gc.face y = Gc.node (Gc.node (Gc.edge y)) := by
          have h7 : Gc.node (Gc.node (Gc.node (Gc.face y))) = Gc.face y :=
            hqc.node_node_node hfybc
          rw [hnfy] at h7
          exact h7.symm
        refine ⟨Gc.edge (Gc.face y), ?_, ?_⟩
        · refine h5.trans ?_
          have h8 := Gc.cface_face (Gc.edge (Gc.node (Gc.node (Gc.edge y))))
          rw [Gc.nodeK (Gc.node (Gc.edge y))] at h8
          rw [hfy]
          exact h8.symm
        · change Gc.CFace (Gc.edge (Gc.edge (Gc.face y))) y
          rw [hplainc.edge_edge]
          exact (Gc.cface_face y).symm

omit [Finite Dc] [Finite Dm] in
/-- Rotating by one less than the length does not depend on how the predecessor
is computed. -/
private theorem rotate_pred_mod {α : Type*} (l : List α) :
    l.rotate (l.length - 1 % l.length) = l.rotate (l.length - 1) := by
  rw [← List.rotate_mod l (l.length - 1 % l.length), ← List.rotate_mod l (l.length - 1)]
  congr 1
  rcases hn : l.length with _ | m
  · decide
  · rcases m with _ | m'
    · decide
    · rw [Nat.mod_eq_of_lt (by omega : (1 : ℕ) < m' + 1 + 1)]

omit [Finite Dc] [Finite Dm] in
/-- The N-image of the perimeter is its rotation. -/
theorem map_node_ring (hemb : Gc.Embeddable rc) : rc.map Gc.node = rc.rotate 1 := by
  refine List.ext_getElem (by simp) fun i hi hi' => ?_
  have hin : i < rc.length := by simpa using hi
  have hmod : (i + 1) % rc.length < rc.length := Nat.mod_lt _ (by omega)
  rw [List.getElem_map, List.getElem_rotate]
  exact (rel_getElem_succ hemb.base.base.base.cycle hin hmod rfl).symm

omit [Finite Dc] [Finite Dm] in
/-- A face-invariant colouring of the perimeter is the rotation of its colouring
of the E-image of the perimeter. -/
theorem map_ring_eq_rotate (hemb : Gc.Embeddable rc) {κ : Dc → Color}
    (hf : ∀ z : Dc, κ (Gc.face z) = κ z) :
    rc.map κ = ((rc.map Gc.edge).map κ).rotate 1 := by
  have h1 : ∀ z : Dc, κ z = κ (Gc.edge (Gc.node z)) := by
    intro z
    rw [← hf (Gc.edge (Gc.node z)), Gc.nodeK]
  have h2 : rc.map κ = (rc.map Gc.node).map (fun w => κ (Gc.edge w)) := by
    rw [List.map_map]
    exact List.map_congr_left fun z _ => h1 z
  rw [h2, map_node_ring hemb, List.map_rotate, List.map_map]
  rfl

omit [Finite Dm] in
/-- The border of the disk projects into the target as the E-image of the
perimeter. -/
theorem map_embdd_ring (hemb : Gc.Embeddable rc) :
    (embdRing Gc rc hemb).map (embdd Gc Gm rc h)
      = (rc.map Gc.edge).map (embed Gc Gm rc h) := by
  have h1 : embdd Gc Gm rc h = (embed Gc Gm rc h) ∘ (embd rc) := rfl
  rw [h1, ← List.map_map, map_embd_ring hemb]

omit [Finite Dm] in
/-- The border of the disk map has as many darts as the perimeter. -/
theorem length_embd_ring (hemb : Gc.Embeddable rc) :
    (embdRing Gc rc hemb).length = rc.length := by
  have h1 := congrArg List.length (map_embd_ring hemb)
  rw [List.length_map, List.length_map] at h1
  exact h1

omit [Finite Dm] in
/-- The border of the remainder map has as many darts as the perimeter. -/
theorem length_embr_ring (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) :
    (embrRing Gc Gm rc h hemb hinj).length = rc.length := by
  have h1 := congrArg List.length (map_embr_ring hemb hinj)
  simp only [List.length_map, List.length_reverse] at h1
  rw [h1, length_embd_ring hemb]

omit [Finite Dm] in
/-- The colouring of the perimeter and the colouring of the border of the
remainder map agree, as lists. -/
theorem map_reverse_ring_eq (hemb : Gc.Embeddable rc)
    (hinj : Function.Injective (embdd Gc Gm rc h)) {k : Dm → Color}
    (hkf : ∀ z : Dc, k (embed Gc Gm rc h (Gc.face z)) = k (embed Gc Gm rc h z)) :
    (rc.reverse).map (fun z => k (embed Gc Gm rc h z))
      = ((embrRing Gc Gm rc h hemb hinj).rotate
          ((embrRing Gc Gm rc h hemb hinj).length - 1)).map
            (fun w => k (embr Gc Gm rc h hemb w)) := by
  have h2 : (embrRing Gc Gm rc h hemb hinj).map (fun w => k (embr Gc Gm rc h hemb w))
      = ((rc.map Gc.edge).map (fun z => k (embed Gc Gm rc h z))).reverse := by
    have h3 : (fun w => k (embr Gc Gm rc h hemb w)) = k ∘ (embr Gc Gm rc h hemb) := rfl
    rw [h3, ← List.map_map, map_embr_ring hemb hinj, List.map_reverse,
      map_embdd_ring hemb, List.map_map]
    rfl
  rw [List.map_rotate, h2, length_embr_ring hemb hinj, List.map_reverse,
    map_ring_eq_rotate hemb hkf, List.reverse_rotate]
  have hlen : ((rc.map Gc.edge).map (fun z => k (embed Gc Gm rc h z))).length = rc.length := by
    simp
  rw [hlen]
  have h5 := rotate_pred_mod
    (((rc.map Gc.edge).map (fun z => k (embed Gc Gm rc h z))).reverse)
  rw [List.length_reverse, hlen] at h5
  exact h5

/-- **The contract colouring of the target gives a contract ring trace matching
a colouring of the remainder map.**  This is the reference's `embed_contract`. -/
theorem embed_contract (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {cc : List Dc}
    (hvc : Gc.ValidContract rc cc) {k : Dm → Color}
    (hk : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) :
    ∃ et, Gc.CcRingTrace cc rc.reverse et ∧
      embedCotrace Gc Gm rc h hemb hplainm hcubm hpre hinj et := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hk1face : ∀ z : Dc,
      k (embed Gc Gm rc h (Gc.face z)) = k (embed Gc Gm rc h z) :=
    fun z => (hk.cface (cface_embed hemb hplainm hcubm hpre hinj (Gc.cface_face z))).symm
  have hmapinsert : Gm.insertE (cc.map (embed Gc Gm rc h))
      = (Gc.insertE cc).map (embed Gc Gm rc h) :=
    insertE_map_embed hemb hplainm hcubm hpre cc
  have hk1cc : Gc.CcColoring cc (fun z => k (embed Gc Gm rc h z)) := by
    refine ⟨?_, hk1face⟩
    have key : ∀ z : Dc, z ∉ rc →
        (k (embed Gc Gm rc h (Gc.edge z)) = k (embed Gc Gm rc h z) ↔ z ∈ Gc.insertE cc) := by
      intro z hz
      rw [embedE hemb hplainm hcubm hpre z, hk.edge, hmapinsert]
      constructor
      · intro hm
        obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hm
        rwa [embed_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
          (hvc.off_ring y hy) hz hyz] at hy
      · intro hm
        exact List.mem_map.mpr ⟨z, hm, rfl⟩
    intro z
    by_cases hz : z ∈ rc
    · have hez : Gc.edge z ∉ rc := (edge_perimeter hemb z).resolve_left (not_not_intro hz)
      have h2 := key (Gc.edge z) hez
      rw [hplainc.edge_edge] at h2
      constructor
      · intro hcon
        have h4 := edge_mem_insertE hplainc (h2.mp hcon.symm)
        rwa [hplainc.edge_edge] at h4
      · intro hcon
        exact (h2.mpr (edge_mem_insertE hplainc hcon)).symm
    · exact key z hz
  refine ⟨trace ((rc.reverse).map (fun z => k (embed Gc Gm rc h z))),
    ⟨_, hk1cc, rfl⟩, ⟨fun w => k (embr Gc Gm rc h hemb w), ⟨?_, ?_⟩, ?_⟩⟩
  · intro w
    change k (Gm.edge (embr Gc Gm rc h hemb w)) ≠ k (embr Gc Gm rc h hemb w)
    intro hcon
    rw [hk.edge, hmapinsert] at hcon
    obtain ⟨y, hy, hyw⟩ := List.mem_map.mp hcon
    have hey : Gc.edge y ∈ Gc.insertE cc := edge_mem_insertE hplainc hy
    have heybc : Gc.edge y ∉ rc := hvc.off_ring _ hey
    refine w.2 ⟨⟨y, hvc.off_ring y hy⟩, ?_, hyw⟩
    intro hmem
    rw [mem_embd_ring_iff hemb] at hmem
    obtain ⟨z, hzrc, hzy⟩ := List.mem_map.mp hmem
    have hzy' : Gc.edge z = y := hzy
    exact heybc (by rw [← hzy', hplainc.edge_edge]; exact hzrc)
  · intro w
    exact (hk.cface ((embed_patch hemb hplainm hcubm hpre hinj).cface_hr w)).symm
  · rw [map_reverse_ring_eq hemb hinj hk1face]

omit [Finite Dc] [Finite Dm] in
/-- A face-invariant colouring of the reversed perimeter is a rotation of the
reversed colouring of the E-image of the perimeter. -/
theorem map_reverse_ring_rotate (hemb : Gc.Embeddable rc) {κ : Dc → Color}
    (hf : ∀ z : Dc, κ (Gc.face z) = κ z) :
    (rc.reverse).map κ = (((rc.map Gc.edge).map κ).reverse).rotate (rc.length - 1) := by
  rw [List.map_reverse, map_ring_eq_rotate hemb hf, List.reverse_rotate]
  have hlen : ((rc.map Gc.edge).map κ).length = rc.length := by simp
  rw [hlen]
  have h5 := rotate_pred_mod (((rc.map Gc.edge).map κ).reverse)
  rw [List.length_reverse, hlen] at h5
  exact h5

/-- **A C-reducible configuration cannot be embedded in a minimal
counter-example.**  This is the reference's `not_embed_reducible`, and the last
link of the Four Colour Theorem's reducibility half. -/
theorem not_embed_reducible (hemb : Gc.Embeddable rc) (hmin : Gm.MinimalCounterExample)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {cc : List Dc}
    (hcred : Gc.CReducible rc cc) : False := by
  classical
  have hplanm : Gm.Planar := hmin.planar
  have hplainm : Gm.Plain := hmin.plain
  have hbridgem : Gm.Bridgeless := hmin.bridgeless
  have hconnm : Gm.Connected := hmin.connected
  have hBm : Gm.BirkhoffRings := hmin.birkhoffRings
  have hcubm : Gm.Cubic := hmin.plainCubicPentagonal.base.cubic
  have hpentm : Gm.Pentagonal := hmin.pentagonal
  have hinj : Function.Injective (embdd Gc Gm rc h) :=
    embdd_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
  -- the image of the contract is valid for the remainder map, so it is coloured
  obtain ⟨k, hk⟩ := hmin.contract_coloring hBm
    (embed_valid_contract hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hinj
      hcred.base)
  obtain ⟨et, hetc, hetr⟩ :=
    embed_contract hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre hinj
      hcred.base hk
  -- C-reducibility turns that into a genuine colouring of the configuration
  obtain ⟨et', hetc', hetr'⟩ := hcred.coclosure et hetc _
    (embed_closure hemb hplanm hplainm hcubm hpre hinj) hetr
  obtain ⟨kc, hkc, hetceq⟩ := hetc'
  obtain ⟨kr, hkr, hetreq⟩ := hetr'
  -- both sides of the patch are coloured, so the target is four-colourable
  refine hmin.noncolorable ?_
  refine ((embed_patch hemb hplainm hcubm hpre hinj).colorable_patch).mpr
    ⟨trace ((embdRing Gc rc hemb).map (fun u => kc (embd rc u))),
      ⟨fun u => kc (embd rc u), ⟨?_, ?_⟩, rfl⟩, ⟨kr, hkr, ?_⟩⟩
  · -- the disk colouring separates E-links
    intro u
    change kc (embdEdge Gc rc u.1) ≠ kc u.1
    by_cases hu : Gc.edge u.1 ∈ rc
    · rw [embdEdge_of_mem hu, ← hkc.face (Gc.edge (Gc.node (Gc.edge u.1))), Gc.nodeK]
      exact hkc.edge u.1
    · rw [embdEdge_of_not_mem hu]
      exact hkc.edge u.1
  · -- the disk colouring is constant on faces
    intro u
    exact (hkc.cface ((cface_embd hemb).mp
      ((embedDisk Gc rc hemb).cface_face u))).symm
  · -- the two ring traces match
    have hEc : (embdRing Gc rc hemb).map (fun u => kc (embd rc u))
        = (rc.map Gc.edge).map kc := by
      have h1 : (fun u => kc (embd rc u)) = kc ∘ (embd rc) := rfl
      rw [h1, ← List.map_map, map_embd_ring hemb]
    rw [hEc, ← trace_reverse]
    rw [map_reverse_ring_rotate hemb hkc.face, trace_rotate] at hetceq
    rw [List.map_rotate, trace_rotate, length_embr_ring hemb hinj] at hetreq
    exact (List.rotate_injective (rc.length - 1) (hetreq.symm.trans hetceq)).symm

end EmbedContract

end Embeddings

end Hypermap

end FourColor

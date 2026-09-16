import FourColor.Jordan
import FourColor.Orbit

/-!
# Edge orbits meet a degenerate or non-crossing dart

In a hypermap with the Jordan curve property, every edge orbit contains a dart
that is either degenerate or whose node image leaves the orbit — the reference's
`Euler_tree`.  It is the combinatorial core of Euler's formula seen as a graph
argument: a connected map with one face is a tree, so it has a terminal node.

This file builds the argument in steps: an unconditional analysis of the arcs
and contours of a hypermap, and then the construction, under the negation of
the statement, of a contour that violates the Jordan curve property.

## Main results

* `Hypermap.exists_face_simple_arc` — every dart lies just after an arc of its
  edge orbit whose darts meet pairwise different faces, and which closes up in
  the face of the dart preceding it.
* `Hypermap.exists_contour` — the contour running along such an arc, a
  duplicate-free contour path covering the same faces.
* `Hypermap.exists_edge_arc` — the rest of the edge orbit, from `face x` back
  to `node (face x)`, avoiding the arc.
* `Hypermap.exists_degenerate_or_not_cross` — the reference's `Euler_tree`.
-/

namespace FourColor

namespace Hypermap

open Equiv Equiv.Perm Function

variable {D : Type*} [Finite D] (G : Hypermap D)

private theorem getLastD_map_range (g : ℕ → D) (n : ℕ) (d : D) :
    ((List.range (n + 1)).map g).getLastD d = g n := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, getLastD_append_cons]
  rfl

private theorem map_range_succ (g : ℕ → D) (n : ℕ) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map fun i => g (i + 1) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- Walking along an edge orbit, the faces met are pairwise different until the
walk first returns to a face it has already met.  Cutting the walk there leaves
an arc `x :: p` of pairwise different faces whose last dart shares a face with
`node (face x)`, the dart just before the arc. -/
theorem exists_face_simple_arc (x₀ : D) :
    ∃ (x : D) (p : List D), G.CEdge x₀ x ∧
      List.IsChain (fun a b => b = G.edge a) (x :: p) ∧
      (x :: p).Pairwise (fun a b => ¬ G.CFace a b) ∧
      G.CFace (p.getLastD x) (G.node (G.face x)) := by
  classical
  set a : ℕ → D := fun i => (G.edge ^ i) x₀ with ha
  have hstep : ∀ i, a (i + 1) = G.edge (a i) := by
    intro i
    simp only [ha, pow_succ']
    rfl
  have ha0 : a 0 = x₀ := by simp [ha]
  have hedge : ∀ i, G.CEdge x₀ (a i) := fun i => ⟨i, by simp [ha]⟩
  -- the walk returns to the face it started from
  have hex : ∃ k, ∃ j, j < k ∧ G.CFace (a j) (a k) := by
    refine ⟨minimalPeriod (G.edge : D → D) x₀, 0, minimalPeriod_pos G.edge x₀, ?_⟩
    have hm : a (minimalPeriod (G.edge : D → D) x₀) = x₀ := pow_minimalPeriod G.edge x₀
    rw [hm, ha0]
  set k := Nat.find hex with hk
  obtain ⟨j, hjk, hface⟩ := Nat.find_spec hex
  -- before the return, the faces met are pairwise different
  have hmin : ∀ k' < k, ∀ j' < k', ¬ G.CFace (a j') (a k') := fun k' hk' j' hj' hc =>
    Nat.find_min hex hk' ⟨j', hj', hc⟩
  -- the arc runs from `a (j+1)` to `a k`
  set g : ℕ → D := fun i => a (j + 1 + i) with hg
  have hgstep : ∀ i, g (i + 1) = G.edge (g i) := fun i => hstep (j + 1 + i)
  obtain ⟨n, hn⟩ : ∃ n, k - j = n + 1 := ⟨k - j - 1, by omega⟩
  have hjn : j + 1 + n = k := by omega
  have hlast : g n = a k := by
    simp only [hg]
    rw [hjn]
  refine ⟨g 0, (List.range n).map fun i => g (i + 1), hedge _, ?_, ?_, ?_⟩
  · rw [← map_range_succ]
    exact isChain_map_range G.edge _ _ hgstep
  · rw [← map_range_succ, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro i i' hi hi' hlt hc
    rw [List.mem_range] at hi hi'
    simp only [hg] at hc
    have hle : j + 1 + i' ≤ k := by omega
    rcases lt_or_eq_of_le hle with hkk | hkk
    · exact hmin _ hkk _ (by omega) hc
    · -- the arc ends where the walk returned
      refine hmin (j + 1 + i) (by omega) j (by omega) ?_
      exact hface.trans (hkk ▸ hc).symm
  · have h2 := getLastD_map_range g n (g 0)
    rw [map_range_succ, getLastD_cons] at h2
    rw [h2, hlast]
    have hg0 : g 0 = G.edge (a j) := hstep j
    rw [hg0, G.edgeK]
    exact hface.symm

/-! ### Face paths

A duplicate-free path inside a single face, from one dart to another.
-/

theorem cface_of_isChain_face {u : D} : ∀ {q : List D},
    List.IsChain (fun a b => b = G.face a) (u :: q) → ∀ w ∈ u :: q, G.CFace u w := by
  intro q
  induction q generalizing u with
  | nil => intro _ w hw; rw [List.mem_singleton.mp hw]
  | cons c q ih =>
    intro hchain w hw
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hchain
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Equiv.Perm.SameCycle.refl _ _
    · have huc : G.CFace u c := ⟨1, by rw [hstep]; simp⟩
      exact huc.trans (ih htail w hw)

theorem exists_perm_path {f : Perm D} {u v : D} (h : f.SameCycle u v) :
    ∃ q : List D, List.IsChain (fun a b => b = f a) (u :: q) ∧
      q.getLastD u = v ∧ (u :: q).Nodup := by
  have h' : Relation.ReflTransGen (fun a b => b = f a) u v :=
    (sameCycle_iff_reflTransGen f u v).mp h
  obtain ⟨p, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h' 
  obtain ⟨q, hq, hnodup, hqlast, -⟩ := List.IsChain.exists_nodup hchain
  refine ⟨q, hq, ?_, hnodup⟩
  rw [hqlast]
  have : (u :: p).getLastD u = p.getLastD u := getLastD_cons u u p
  rw [← this]
  have h2 : (u :: p).getLast (List.cons_ne_nil u p) = v := hlast
  match p with
  | [] => simpa using h2.symm ▸ rfl
  | c :: p => exact h2

theorem exists_face_path {u v : D} (h : G.CFace u v) :
    ∃ q : List D, List.IsChain (fun a b => b = G.face a) (u :: q) ∧
      q.getLastD u = v ∧ (u :: q).Nodup := exists_perm_path h

/-- A duplicate-free contour path inside a single node, from one dart to
another: each N-link `node u — u` is a contour link. -/
theorem exists_node_clink_path {u v : D} (h : G.CNode u v) :
    ∃ q : List D, List.IsChain G.Clink (u :: q) ∧ q.getLastD u = v ∧ (u :: q).Nodup := by
  have h' : (G.node⁻¹).SameCycle u v := by rwa [Equiv.Perm.sameCycle_inv]
  obtain ⟨q, hchain, hlast, hnodup⟩ := exists_perm_path h'
  refine ⟨q, hchain.imp fun a b hab => Or.inl ?_, hlast, hnodup⟩
  rw [hab]
  simp

/-! ### Reading a chain backwards

Two list lemmas used to locate the `face` preimage of a dart of the contour.
-/

/-- A dart of a duplicate-free list that occurs before the last position is not
the last dart. -/
theorem ne_getLastD_of_mem_dropLast : ∀ {l : List D}, l.Nodup → ∀ {t d : D},
    t ∈ l.dropLast → t ≠ l.getLastD d := by
  intro l
  induction l with
  | nil => intro _ t d h; simp at h
  | cons a l ih =>
    rcases l with _ | ⟨b, l⟩
    · intro _ t d h; simp at h
    · intro hnodup t d h
      rw [getLastD_cons]
      rw [List.dropLast_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · intro heq
        refine (List.nodup_cons.mp hnodup).1 ?_
        rw [← h, heq, getLastD_cons]
        exact getLastD_mem_cons b l
      · exact ih (List.nodup_cons.mp hnodup).2 h

/-- If the image of a dart under `f` lies on an `f`-chain then so does the dart
itself, and before the last position — unless it is the preimage of the head. -/
theorem mem_dropLast_of_apply_mem {f : Perm D} {u : D} : ∀ {q : List D},
    List.IsChain (fun a b => b = f a) (u :: q) → ∀ t, f t ∈ u :: q →
      t = f⁻¹ u ∨ t ∈ (u :: q).dropLast := by
  intro q
  induction q generalizing u with
  | nil =>
    intro _ t ht
    have hh : f t = u := List.mem_singleton.mp ht
    exact Or.inl (by rw [← hh]; simp)
  | cons a q ih =>
    intro hchain t ht
    obtain ⟨rfl, htail⟩ := List.isChain_cons_cons.mp hchain
    rcases List.mem_cons.mp ht with h | h
    · exact Or.inl (by rw [← h]; simp)
    · refine Or.inr ?_
      rcases ih htail t h with h' | h'
      · rw [h']
        simp
      · rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ h'

/-! ### The contour along a face-simple arc

The contour runs around the face of each dart of the arc, from its `face` image
back to the dart itself, and then jumps to the next face by a reverse N-link.
-/

theorem exists_contour : ∀ (p : List D) (x z : D),
    List.IsChain (fun a b => b = G.edge a) (x :: p) →
    (x :: p).Pairwise (fun a b => ¬ G.CFace a b) →
    G.CFace (p.getLastD x) z →
    ∃ q : List D,
      List.IsChain G.Clink (G.face x :: q) ∧
      q.getLastD (G.face x) = z ∧
      (G.face x :: q).Nodup ∧
      (∀ t, (∃ w ∈ G.face x :: q, G.CFace t w) ↔ ∃ w ∈ x :: p, G.CFace t w) ∧
      ∀ t, G.face t ∈ G.face x :: q →
        (t ∈ G.face x :: q ∧ t ≠ z) ∨ t = p.getLastD x := by
  intro p
  induction p with
  | nil =>
    intro x z _ _ hlast
    have hfz : G.CFace (G.face x) z :=
      (G.cface_face x).symm.trans hlast
    obtain ⟨q, hchain, hqlast, hnodup⟩ := exists_face_path G hfz
    refine ⟨q, hchain.imp fun a b hab => Or.inr hab.symm, hqlast, hnodup, fun t => ?_, ?_⟩
    · have hall := cface_of_isChain_face G hchain
      constructor
      · rintro ⟨w, hw, htw⟩
        exact ⟨x, List.mem_cons_self, htw.trans ((hall w hw).symm.trans (G.cface_face x).symm)⟩
      · rintro ⟨w, hw, htw⟩
        rw [List.mem_singleton.mp hw] at htw
        exact ⟨G.face x, List.mem_cons_self, htw.trans (G.cface_face x)⟩
    · intro t ht
      rcases mem_dropLast_of_apply_mem hchain t ht with h | h
      · refine Or.inr ?_
        rw [h]
        simp
      · refine Or.inl ⟨List.dropLast_subset _ h, ?_⟩
        have hne := ne_getLastD_of_mem_dropLast (d := G.face x) hnodup h
        rwa [getLastD_cons, hqlast] at hne
  | cons y p ih =>
    intro x z hchain hsimple hlast
    obtain ⟨hxy, hchain'⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨hxnot, hsimple'⟩ := List.pairwise_cons.mp hsimple
    -- the contour for the rest of the arc
    have hlast' : G.CFace (p.getLastD y) z := by rwa [getLastD_cons] at hlast
    obtain ⟨q₂, hq₂chain, hq₂last, hq₂nodup, hq₂band, hq₂pre⟩ := ih y z hchain' hsimple' hlast'
    -- the face of `x`, walked from `face x` back to `x`
    obtain ⟨q₁, hq₁chain, hq₁last, hq₁nodup⟩ := exists_face_path G (G.cface_face x).symm
    have hall₁ := cface_of_isChain_face G hq₁chain
    -- the two pieces are disjoint, because their faces are
    have hdisj : ∀ w ∈ G.face x :: q₁, w ∉ G.face y :: q₂ := by
      intro w hw hw₂
      obtain ⟨v, hv, hcv⟩ := (hq₂band w).mp ⟨w, hw₂, Equiv.Perm.SameCycle.refl _ _⟩
      exact hxnot v hv ((G.cface_face x).trans ((hall₁ w hw).trans hcv))
    refine ⟨q₁ ++ G.face y :: q₂, ?_, ?_, ?_, fun t => ?_, ?_⟩
    · refine isChain_append_cons (hq₁chain.imp fun a b hab => Or.inr hab.symm) ?_ hq₂chain
      -- the last dart of the first piece is `x`, and `x = node (face y)`
      rw [hq₁last]
      refine Or.inl ?_
      rw [hxy, G.edgeK]
    · rw [getLastD_append_cons, hq₂last]
    · rw [← List.cons_append]
      exact List.nodup_append.mpr ⟨hq₁nodup, hq₂nodup,
        fun a ha b hb hab => hdisj a ha (hab ▸ hb)⟩
    · rw [← List.cons_append]
      constructor
      · rintro ⟨w, hw, htw⟩
        rcases List.mem_append.mp hw with hw | hw
        · exact ⟨x, List.mem_cons_self,
            htw.trans ((hall₁ w hw).symm.trans (G.cface_face x).symm)⟩
        · obtain ⟨v, hv, hcv⟩ := (hq₂band t).mp ⟨w, hw, htw⟩
          exact ⟨v, List.mem_cons_of_mem _ hv, hcv⟩
      · rintro ⟨w, hw, htw⟩
        rcases List.mem_cons.mp hw with hwx | hw
        · refine ⟨G.face x, List.mem_append_left _ List.mem_cons_self, ?_⟩
          rw [hwx] at htw
          exact htw.trans (G.cface_face x)
        · obtain ⟨v, hv, hcv⟩ := (hq₂band t).mpr ⟨w, hw, htw⟩
          exact ⟨v, List.mem_append_right _ hv, hcv⟩
    · intro t ht
      rw [← List.cons_append] at ht
      rcases List.mem_append.mp ht with ht | ht
      · -- the face image lies on the complete face cycle of `x`
        have hmem : t ∈ G.face x :: q₁ := by
          rcases mem_dropLast_of_apply_mem hq₁chain t ht with h | h
          · have hx' : t = x := by rw [h]; simp
            have hxm : q₁.getLastD (G.face x) ∈ G.face x :: q₁ := getLastD_mem_cons _ _
            rw [hq₁last] at hxm
            rw [hx']
            exact hxm
          · exact List.dropLast_subset _ h
        refine Or.inl ⟨?_, ?_⟩
        · rw [← List.cons_append]
          exact List.mem_append_left _ hmem
        · intro htz
          refine hdisj t hmem ?_
          have hzm : q₂.getLastD (G.face y) ∈ G.face y :: q₂ := getLastD_mem_cons _ _
          rw [hq₂last] at hzm
          rw [htz]
          exact hzm
      · -- the face image lies on the contour of the rest of the arc
        rcases hq₂pre t ht with ⟨h₁, h₂⟩ | h
        · refine Or.inl ⟨?_, h₂⟩
          rw [← List.cons_append]
          exact List.mem_append_right _ h₁
        · rw [getLastD_cons]
          exact Or.inr h

/-! ### The tree hypothesis closes the edge orbit under `node`

If every dart of an edge orbit has its node image on the same orbit, the orbit
is closed under `node`, hence under `node⁻¹`, and so contains `face x` for each
of its darts `x` — because `face x` is the `node`-preimage of `edge⁻¹ x`.
-/

variable {G} {x₀ : D}

theorem cedge_node (H : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y)) {y : D}
    (hy : G.CEdge x₀ y) : G.CEdge x₀ (G.node y) := hy.trans (H y hy)

theorem cedge_node_pow (H : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y)) {y : D}
    (hy : G.CEdge x₀ y) : ∀ n : ℕ, G.CEdge x₀ ((G.node ^ n) y) := by
  intro n
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    have hstep : (G.node ^ (n + 1)) y = G.node ((G.node ^ n) y) := by
      rw [pow_succ']
      rfl
    rw [hstep]
    exact cedge_node H ih

theorem cedge_node_inv (H : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y)) {y : D}
    (hy : G.CEdge x₀ y) : G.CEdge x₀ (G.node⁻¹ y) := by
  have hpos : 0 < orderOf G.node := orderOf_pos G.node
  have hmul : G.node * G.node ^ (orderOf G.node - 1) = 1 := by
    rw [← pow_succ', show orderOf G.node - 1 + 1 = orderOf G.node by omega]
    exact pow_orderOf_eq_one G.node
  have hP : G.node⁻¹ = G.node ^ (orderOf G.node - 1) := inv_eq_of_mul_eq_one_right hmul
  rw [hP]
  exact cedge_node_pow H hy _

/-- Under the tree hypothesis, the face image of a dart of the orbit is again on
the orbit. -/
theorem cedge_face (H : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y)) {x : D}
    (hx : G.CEdge x₀ x) : G.CEdge x₀ (G.face x) := by
  have hnf : G.node (G.face x) = G.edge⁻¹ x :=
    Equiv.Perm.eq_inv_iff_eq.mpr (G.faceK x)
  have hface : G.face x = G.node⁻¹ (G.edge⁻¹ x) := Equiv.Perm.eq_inv_iff_eq.mpr hnf
  have hedge : G.CEdge x₀ (G.edge⁻¹ x) := hx.trans ⟨-1, by simp⟩
  rw [hface]
  exact cedge_node_inv H hedge

/-! ### The edge arc from `face x` back to `node (face x)`

Indexing the edge orbit from `x`, the arc occupies an initial segment and
`face x` lies strictly after it, so the darts from `face x` to the last dart of
the orbit avoid the arc entirely.
-/

theorem mem_pow_of_isChain {f : Perm D} {x : D} : ∀ {p : List D},
    List.IsChain (fun a b => b = f a) (x :: p) → ∀ w ∈ x :: p, ∃ j ≤ p.length, w = (f ^ j) x := by
  intro p
  induction p generalizing x with
  | nil =>
    intro _ w hw
    exact ⟨0, le_rfl, by simpa using List.mem_singleton.mp hw⟩
  | cons c p ih =>
    intro hchain w hw
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hchain
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · obtain ⟨j, hj, rfl⟩ := ih htail w hw
      refine ⟨j + 1, by simpa using hj, ?_⟩
      rw [hstep, ← Equiv.Perm.mul_apply, ← pow_succ]
  
/-- A non-degenerate dart of a face-simple arc has its face image off the
arc. -/
theorem face_not_mem_arc (hdeg : ∀ y, G.CEdge x₀ y → ¬ G.Clink y y) {x : D} {p : List D}
    (hx : G.CEdge x₀ x) (hsimple : (x :: p).Pairwise fun a b => ¬ G.CFace a b) :
    G.face x ∉ x :: p := by
  intro hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact hdeg x hx (Or.inr h)
  · exact (List.pairwise_cons.mp hsimple).1 _ h (G.cface_face x)

theorem pow_mem_of_isChain {f : Perm D} {x : D} : ∀ {p : List D},
    List.IsChain (fun a b => b = f a) (x :: p) → ∀ j ≤ p.length, (f ^ j) x ∈ x :: p := by
  intro p
  induction p generalizing x with
  | nil =>
    intro _ j hj
    rw [Nat.le_zero.mp hj]
    simpa using List.mem_cons_self
  | cons c p ih =>
    intro hchain j hj
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hchain
    match j with
    | 0 => simpa using List.mem_cons_self
    | j + 1 =>
      have hmem := ih htail j (by simpa using hj)
      have heq : (f ^ (j + 1)) x = (f ^ j) c := by
        rw [hstep, ← Equiv.Perm.mul_apply, ← pow_succ]
      rw [heq]
      exact List.mem_cons_of_mem _ hmem

theorem pow_mem_tail_of_isChain {f : Perm D} {x : D} {c : D} {p : List D}
    (hchain : List.IsChain (fun a b => b = f a) (x :: c :: p)) :
    ∀ j, 1 ≤ j → j ≤ p.length + 1 → (f ^ j) x ∈ c :: p := by
  intro j h1 h2
  obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hchain
  match j with
  | 0 => omega
  | j + 1 =>
    have heq : (f ^ (j + 1)) x = (f ^ j) c := by
      rw [hstep, ← Equiv.Perm.mul_apply, ← pow_succ]
    rw [heq]
    exact pow_mem_of_isChain htail j (by omega)

theorem exists_edge_arc (H : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y)) {x : D} {p : List D}
    (hx : G.CEdge x₀ x) (hchain : List.IsChain (fun a b => b = G.edge a) (x :: p))
    (hnodup : (x :: p).Nodup) (hfx : G.face x ∉ x :: p) :
    ∃ q : List D, List.IsChain (fun a b => b = G.edge a) (G.face x :: q) ∧
      q.getLastD (G.face x) = G.node (G.face x) ∧ ∀ w ∈ G.face x :: q, w ∉ x :: p := by
  classical
  set a : ℕ → D := fun i => (G.edge ^ i) x with ha
  set m := Function.minimalPeriod (G.edge : D → D) x with hm
  have hmpos : 0 < m := minimalPeriod_pos G.edge x
  have ham : a m = x := pow_minimalPeriod G.edge x
  have hastep : ∀ j, a (j + 1) = G.edge (a j) := by
    intro j
    simp only [ha, pow_succ']
    rfl
  have hinj : ∀ i₁ < m, ∀ i₂ < m, a i₁ = a i₂ → i₁ = i₂ := by
    intro i₁ h₁ i₂ h₂ heq
    refine Function.iterate_injOn_Iio_minimalPeriod (f := (G.edge : D → D)) (x := x) h₁ h₂ ?_
    simpa [ha, Equiv.Perm.iterate_eq_pow] using heq
  -- the arc is shorter than the orbit, since its darts are distinct
  have hlen : p.length < m := by
    by_contra hcon
    push_neg at hcon
    match p with
    | [] =>
      simp only [List.length_nil] at hcon
      omega
    | c :: p' =>
      have hmem : a m ∈ c :: p' := by
        refine pow_mem_tail_of_isChain hchain m hmpos ?_
        simpa using hcon
      rw [ham] at hmem
      exact (List.nodup_cons.mp hnodup).1 hmem
  -- `face x` lies on the orbit, past the arc
  have hfmem : G.CEdge x (G.face x) := hx.symm.trans (cedge_face H hx)
  obtain ⟨i, him, hfi⟩ : ∃ i, i < m ∧ a i = G.face x := by
    obtain ⟨w, hw, hwf⟩ : ∃ w ∈ orbitList G.edge x, w = G.face x :=
      ⟨G.face x, mem_orbitList.mpr hfmem, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact ⟨i, List.mem_range.mp hi, hwf⟩
  have hlt : p.length < i := by
    by_contra hcon
    push_neg at hcon
    exact hfx (hfi ▸ pow_mem_of_isChain hchain i hcon)
  -- the rest of the orbit, from `face x` to its `node` preimage
  have hmi : m - i = (m - i - 1) + 1 := by omega
  refine ⟨(List.range (m - i - 1)).map fun j => a (i + 1 + j), ?_, ?_, ?_⟩
  · have hcons : (G.face x :: (List.range (m - i - 1)).map fun j => a (i + 1 + j))
        = (List.range (m - i)).map fun j => a (i + j) := by
      conv_rhs => rw [hmi]
      rw [map_range_succ]
      congr 1
      · rw [Nat.add_zero, hfi]
      · exact List.map_congr_left fun j _ => by congr 1; omega
    rw [hcons]
    exact isChain_map_range G.edge _ _ fun j => hastep (i + j)
  · have hlast : ((List.range (m - i - 1)).map fun j => a (i + 1 + j)).getLastD (G.face x)
        = a (m - 1) := by
      match hmi1 : m - i - 1 with
      | 0 =>
        have hii : i = m - 1 := by omega
        simp only [List.range_zero, List.map_nil, List.getLastD_nil]
        rw [← hfi, hii]
      | n + 1 =>
        rw [getLastD_map_range]
        congr 1
        omega
    rw [hlast]
    have hedge : G.edge (a (m - 1)) = x := by
      have := hastep (m - 1)
      rw [show m - 1 + 1 = m by omega, ham] at this
      exact this.symm
    have hnf : G.node (G.face x) = G.edge⁻¹ x :=
      Equiv.Perm.eq_inv_iff_eq.mpr (G.faceK x)
    rw [hnf, ← hedge]
    simp
  · intro w hw hwarc
    obtain ⟨j', hj', hwj⟩ := mem_pow_of_isChain hchain w hwarc
    rcases List.mem_cons.mp hw with rfl | hw
    · have hj'i : a j' = a i := by
        simp only [ha] at hfi ⊢
        rw [← hwj]
        exact hfi.symm
      have : j' = i := hinj _ (by omega) _ him hj'i
      omega
    · obtain ⟨j, hj, hwij⟩ := List.mem_map.mp hw
      rw [List.mem_range] at hj
      have heq : a j' = a (i + 1 + j) := by
        simp only [ha] at hwij ⊢
        rw [← hwj]
        exact hwij.symm
      have : j' = i + 1 + j := hinj _ (by omega) _ (by omega) heq
      omega

/-! ### Walking a node orbit is a contour path

Each N-link `node u — u` is a contour link, so the node orbit of a dart,
traversed backwards, is a contour path from its `node` preimage to it.
-/

variable (G)

theorem isChain_clink_reverse_orbit_node (y : D) :
    List.IsChain G.Clink (orbitList G.node y).reverse := by
  rw [List.isChain_reverse]
  exact (isChain_orbitList G.node y).imp fun a b hab => Or.inl hab

theorem getLastD_reverse_orbit_node (y : D) :
    (orbitList G.node y).reverse.getLastD y = y := by
  have hne : orbitList G.node y ≠ [] := orbitList_ne_nil G.node y
  match h : orbitList G.node y with
  | [] => exact absurd h hne
  | c :: q =>
    have hc : c = y := by
      have := head_orbitList G.node y
      rw [h] at this
      simpa using this
    rw [List.reverse_cons]
    rw [getLastD_append_cons]
    simpa using hc

/-! ### Extending the contour

The *extension* of a contour `c :: q₁` running from `c` to `node c` is a
contour path that starts at `node c` and whose darts all avoid the contour.  It
is grown one link at a time along the reverse of the edge arc: the Jordan
hypothesis keeps it off the contour at an N-link, and the last conclusion of
`exists_contour` keeps it off at an F-link.
-/

/-- A contour path from `n` to `y` whose darts after `n` all avoid `c`. -/
def AvoidPath (c : List D) (n y : D) : Prop :=
  ∃ q : List D, List.IsChain G.Clink (n :: q) ∧ q.getLastD n = y ∧ ∀ w ∈ q, w ∉ c

variable {G}

/-- The empty extension. -/
theorem avoidPath_refl (c : List D) (n : D) : G.AvoidPath c n n :=
  ⟨[], List.IsChain.singleton n, rfl, by simp⟩

/-- Extending an avoiding path by one contour link. -/
theorem AvoidPath.snoc {c : List D} {n y w : D} (h : G.AvoidPath c n y)
    (hlink : G.Clink y w) (hw : w ∉ c) : G.AvoidPath c n w := by
  obtain ⟨q, hchain, hlast, havoid⟩ := h
  refine ⟨q ++ [w], ?_, ?_, ?_⟩
  · rw [← List.cons_append]
    exact isChain_append_cons hchain (by rw [hlast]; exact hlink) (List.IsChain.singleton w)
  · rw [getLastD_append_cons]
    rfl
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact havoid u hu
    · rw [List.mem_singleton.mp hu]
      exact hw

/-- **The Jordan hypothesis blocks the extension.**  If the extension of a
contour `c :: q₁` from `c` to `node c` reaches the `node` image of a dart `z`,
then `z` does not lie on the contour past its first dart: the contour followed
by the extension would be a Moebius path, since `node c` is the last dart of
the contour and hence lies at or after any occurrence of `z` in `q₁`. -/
theorem not_mem_of_avoidPath (hJ : G.Jordan) {c z : D} {q₁ : List D}
    (hchain : List.IsChain G.Clink (c :: q₁)) (hnodup : (c :: q₁).Nodup)
    (hlast : q₁.getLastD c = G.node c)
    (h : G.AvoidPath (c :: q₁) (G.node c) (G.node z)) : z ∉ q₁ := by
  intro hz
  obtain ⟨q₂, h₂chain, h₂last, h₂avoid⟩ := h
  -- cut the loops out of the extension
  obtain ⟨q, hq, hqnodup, hqlast, hqsub⟩ := List.IsChain.exists_nodup h₂chain
  have hjoin : List.IsChain G.Clink (c :: (q₁ ++ q)) := by
    rw [← List.cons_append]
    cases q with
    | nil => simpa using hchain
    | cons a q' =>
      obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hq
      exact isChain_append_cons hchain (by rw [hlast]; exact hstep) htail
  have hjlast : (q₁ ++ q).getLastD c = q.getLastD (G.node c) := by
    cases q with
    | nil => simpa using hlast
    | cons a q' => rw [getLastD_append_cons, getLastD_cons]
  have hnodez : G.node z = (q₁ ++ q).getLastD c := by
    rw [hjlast, hqlast, h₂last]
  have hjnodup : (c :: (q₁ ++ q)).Nodup := by
    rw [← List.cons_append]
    refine List.nodup_append.mpr ⟨hnodup, (List.nodup_cons.mp hqnodup).2, ?_⟩
    intro a ha b hb hab
    exact h₂avoid b (hqsub b hb) (hab ▸ ha)
  have hmem2 : Mem2 (q₁ ++ q) z (G.node c) := by
    obtain ⟨q₃, q₄, rfl⟩ := List.append_of_mem hz
    refine ⟨q₃, q₄ ++ q, by simp, ?_⟩
    have hnc : G.node c = q₄.getLastD z := by rw [← hlast, getLastD_append_cons]
    rcases List.mem_cons.mp (getLastD_mem_cons z q₄) with h' | h'
    · exact Or.inl (by rw [hnc, h'])
    · exact Or.inr (by rw [hnc]; exact List.mem_append_left _ h')
  exact hJ _ (G.moebiusPath_of_data ⟨hjnodup, hjoin, hnodez, hmem2⟩)

/-- One backward N-link step of the extension: if the extension reaches
`node z` off the contour, it extends to `z`, still off the contour. -/
theorem avoidPath_node (hJ : G.Jordan) {c z : D} {q₁ : List D}
    (hchain : List.IsChain G.Clink (c :: q₁)) (hnodup : (c :: q₁).Nodup)
    (hlast : q₁.getLastD c = G.node c) (hz : G.node z ∉ c :: q₁)
    (h : G.AvoidPath (c :: q₁) (G.node c) (G.node z)) :
    z ∉ c :: q₁ ∧ G.AvoidPath (c :: q₁) (G.node c) z := by
  have hznot : z ∉ c :: q₁ := by
    intro hmem
    rcases List.mem_cons.mp hmem with h' | h'
    · refine hz ?_
      have hnm : q₁.getLastD c ∈ c :: q₁ := getLastD_mem_cons c q₁
      rw [hlast] at hnm
      rw [h']
      exact hnm
    · exact not_mem_of_avoidPath hJ hchain hnodup hlast h h'
  exact ⟨hznot, h.snoc (G.clink_node z) hznot⟩

/-- Walking a node orbit backwards, one N-link at a time: if the extension
reaches the last dart of an `n`-chain off the contour, it reaches its first
dart off the contour. -/
theorem avoidPath_node_walk (hJ : G.Jordan) {c : D} {q₁ : List D}
    (hchain : List.IsChain G.Clink (c :: q₁)) (hnodup : (c :: q₁).Nodup)
    (hlast : q₁.getLastD c = G.node c) : ∀ (r : List D) (u : D),
      List.IsChain (fun a b => b = G.node a) (u :: r) →
      r.getLastD u ∉ c :: q₁ → G.AvoidPath (c :: q₁) (G.node c) (r.getLastD u) →
      u ∉ c :: q₁ ∧ G.AvoidPath (c :: q₁) (G.node c) u := by
  intro r
  induction r with
  | nil => intro u _ hnot h; exact ⟨hnot, h⟩
  | cons a r ih =>
    intro u hu hnot h
    obtain ⟨rfl, htail⟩ := List.isChain_cons_cons.mp hu
    rw [getLastD_cons] at hnot h
    obtain ⟨hanot, ha⟩ := ih _ htail hnot h
    exact avoidPath_node hJ hchain hnodup hlast hanot ha

/-- One F-link step of the extension.  The last conclusion of `exists_contour`
is what forces the new dart off the contour: an F-link into the contour would
put its source on the contour, where the extension cannot be. -/
theorem avoidPath_face {c z₁ y : D} {q₁ : List D}
    (hA : ∀ t, G.face t ∈ c :: q₁ → (t ∈ c :: q₁ ∧ t ≠ G.node c) ∨ t = z₁)
    (hy : y ≠ z₁) (h : G.AvoidPath (c :: q₁) (G.node c) y) :
    G.face y ∉ c :: q₁ ∧ G.AvoidPath (c :: q₁) (G.node c) (G.face y) := by
  have hfy : G.face y ∉ c :: q₁ := by
    intro hmem
    rcases hA y hmem with ⟨hy₁, hy₂⟩ | hy₁
    · obtain ⟨q₂, -, h₂last, h₂avoid⟩ := h
      have hym : q₂.getLastD (G.node c) ∈ G.node c :: q₂ := getLastD_mem_cons _ _
      rw [h₂last] at hym
      rcases List.mem_cons.mp hym with h' | h'
      · exact hy₂ h'
      · exact h₂avoid y h' hy₁
    · exact hy hy₁
  exact ⟨hfy, h.snoc (G.clink_face y) hfy⟩

/-- **The extension reaches every dart of the edge arc.**  Walking the arc
backwards from `node c`, each edge step contributes an F-link followed by a
walk down a node orbit. -/
theorem avoidPath_edge_arc (hJ : G.Jordan) {c z₁ : D} {q₁ : List D}
    (hchain : List.IsChain G.Clink (c :: q₁)) (hnodup : (c :: q₁).Nodup)
    (hlast : q₁.getLastD c = G.node c)
    (hA : ∀ t, G.face t ∈ c :: q₁ → (t ∈ c :: q₁ ∧ t ≠ G.node c) ∨ t = z₁) :
    ∀ (p₂ : List D) (y : D), List.IsChain (fun a b => b = G.edge a) (y :: p₂) →
      p₂.getLastD y = G.node c → z₁ ∉ p₂ → G.AvoidPath (c :: q₁) (G.node c) y := by
  intro p₂
  induction p₂ with
  | nil =>
    intro y _ hy _
    simp only [List.getLastD_nil] at hy
    rw [hy]
    exact avoidPath_refl _ _
  | cons a p ih =>
    intro y hy hylast hz₁
    obtain ⟨rfl, htail⟩ := List.isChain_cons_cons.mp hy
    rw [getLastD_cons] at hylast
    have hane : G.edge y ≠ z₁ := fun h => hz₁ (h ▸ List.mem_cons_self)
    have hnz : z₁ ∉ p := fun h => hz₁ (List.mem_cons_of_mem _ h)
    obtain ⟨hfnot, hf⟩ := avoidPath_face hA hane (ih (G.edge y) htail hylast hnz)
    -- the node walk from `face (edge y) = node⁻¹ y` down to `y`
    have hsc : G.node.SameCycle y (G.face (G.edge y)) := by
      have h' := G.cnode_node (G.face (G.edge y))
      rw [G.edgeK y] at h'
      exact h'.symm
    obtain ⟨r, hrchain, hrlast, -⟩ := exists_perm_path hsc
    refine (avoidPath_node_walk hJ hchain hnodup hlast r y hrchain ?_ ?_).2
    · rw [hrlast]; exact hfnot
    · rw [hrlast]; exact hf

/-- **`Euler_tree`.**  In a hypermap with the Jordan curve property, every edge
orbit contains a dart that is degenerate, or whose node image leaves the orbit.

Assuming otherwise, the edge orbit of `x₀` is closed under `node`; the contour
along a face-simple arc of the orbit then extends along the edge arc from
`face x` back to `node (face x)`, and reaching the head of that arc is absurd
because it lies on the contour. -/
theorem exists_degenerate_or_not_cross (hJ : G.Jordan) (x₀ : D) :
    ∃ y, G.CEdge x₀ y ∧ (G.Clink y y ∨ ¬ G.CEdge y (G.node y)) := by
  by_contra hcon
  have Hdeg : ∀ y, G.CEdge x₀ y → ¬ G.Clink y y := fun y hy hd => hcon ⟨y, hy, Or.inl hd⟩
  have Hnode : ∀ y, G.CEdge x₀ y → G.CEdge y (G.node y) := by
    intro y hy
    by_contra hne
    exact hcon ⟨y, hy, Or.inr hne⟩
  obtain ⟨x, p, hx, hchain, hsimple, hlastface⟩ := exists_face_simple_arc G x₀
  obtain ⟨q₁, hq₁chain, hq₁last, hq₁nodup, -, hA⟩ :=
    exists_contour G p x (G.node (G.face x)) hchain hsimple hlastface
  have hnodup : (x :: p).Nodup := by
    refine hsimple.imp ?_
    intro a b hab heq
    exact hab (heq ▸ Equiv.Perm.SameCycle.refl G.face a)
  have hfx : G.face x ∉ x :: p := face_not_mem_arc Hdeg hx hsimple
  obtain ⟨p₂, hp₂chain, hp₂last, hp₂avoid⟩ := exists_edge_arc Hnode hx hchain hnodup hfx
  have hz₁ : p.getLastD x ∉ p₂ := fun h =>
    hp₂avoid _ (List.mem_cons_of_mem _ h) (getLastD_mem_cons x p)
  obtain ⟨q, -, hqlast, hqavoid⟩ :=
    avoidPath_edge_arc hJ hq₁chain hq₁nodup hq₁last hA p₂ (G.face x) hp₂chain hp₂last hz₁
  have hmem : q.getLastD (G.node (G.face x)) ∈ G.node (G.face x) :: q :=
    getLastD_mem_cons _ _
  rw [hqlast] at hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact Hdeg _ (cedge_face Hnode hx) (Or.inl h)
  · exact hqavoid _ h List.mem_cons_self

end Hypermap

end FourColor

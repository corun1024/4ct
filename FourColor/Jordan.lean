import FourColor.Euler

/-!
# Planarity implies the Jordan curve property

A hypermap of genus zero has no Moebius path.  The proof is a minimal
counterexample argument through the Walkup construction: a Moebius path in a
planar hypermap is pushed into one of the three smaller planar transforms,
where the induction hypothesis rules it out.  Each step pins down more of the
structure of the counterexample, until the hypermap is so small that the Euler
formula itself contradicts planarity.

## Main results

* `Hypermap.mem_of_moebiusData` — a Moebius path in a minimal counterexample
  passes through every dart.
-/

namespace FourColor

namespace Hypermap

open Equiv Equiv.Perm

/-! ### List helpers -/

section ListHelpers

variable {α β : Type*}

private theorem getLastD_mem_cons (x : α) (p : List α) : p.getLastD x ∈ x :: p := by
  match p with
  | [] => simp
  | y :: p => exact List.mem_cons_of_mem _ (List.getLast_mem _)

private theorem getLastD_map (f : α → β) (p : List α) (a : α) :
    (p.map f).getLastD (f a) = f (p.getLastD a) := by
  match p with
  | [] => rfl
  | y :: p =>
    show ((y :: p).map f).getLast (by simp) = f ((y :: p).getLast (by simp))
    rw [List.getLast_map]

private theorem getLastD_cons (x y : α) (p : List α) :
    (y :: p).getLastD x = p.getLastD y := by
  match p with
  | [] => rfl
  | c :: p => rfl

end ListHelpers

variable {D : Type*} [DecidableEq D] (G : Hypermap D)

/-! ### A minimal counterexample meets every dart

If a dart lies outside a Moebius path, deleting it leaves the path intact in
the transform, so the transform has a Moebius path of its own.
-/

theorem mem_of_moebiusData (hJE : ∀ w : D, (G.walkupE w).Jordan) {x t : D}
    {p : List D} (hd : G.MoebiusData x p t) (z : D) : z ∈ x :: p := by
  by_contra hz
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hne : ∀ w ∈ x :: p, w ≠ z := fun w hw hc => hz (hc ▸ hw)
  have hneP : ∀ w ∈ p, w ≠ z := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  have hx : x ≠ z := hne x List.mem_cons_self
  have ht : t ≠ z := hne t (List.mem_cons_of_mem _ hmem2.mem_left)
  have hnx : G.node x ≠ z := hne _ (List.mem_cons_of_mem _ hmem2.mem_right)
  have hntz : G.node t ≠ z := by
    rw [hnt]
    exact hne _ (getLastD_mem_cons x p)
  set q : List (Walkup G z) := p.attachWith (· ≠ z) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmap : ((⟨x, hx⟩ : Walkup G z) :: q).map Subtype.val = x :: p := by
    rw [List.map_cons, hmapq]
  have hnodeu : (G.walkupE z).node (⟨x, hx⟩ : Walkup G z) = ⟨G.node x, hnx⟩ :=
    Subtype.ext (skip_val_of_ne (u := (⟨x, hx⟩ : Walkup G z)) hnx)
  refine hJE z _ ((G.walkupE z).moebiusPath_of_data (x := ⟨x, hx⟩) (p := q)
    (t := ⟨t, ht⟩) ⟨?_, ?_, ?_, ?_⟩)
  · exact List.Nodup.of_map Subtype.val (by rw [hmap]; exact hnodup)
  · exact isChain_clink_walkupE G z (by rw [hmap]; exact hchain)
  · refine Subtype.ext ?_
    rw [walkupE_node, skip_val_of_ne (u := (⟨t, ht⟩ : Walkup G z)) hntz]
    have := getLastD_map (Subtype.val (p := fun w : D => w ≠ z)) q ⟨x, hx⟩
    rw [hmapq] at this
    rw [hnt, this]
  · rw [hnodeu]
    exact (Mem2.map_iff (f := (Subtype.val : Walkup G z → D)) Subtype.val_injective).mp
      (by rw [hmapq]; exact hmem2)

/-! ### The first link of a minimal counterexample is an F-link

A reverse N-link at the head of a Moebius path can be cut away: deleting the
head leaves a Moebius path in the transform, because the crossing N-link the
path carries is exactly the one at the head.
-/

theorem face_head_of_moebiusData (hJE : ∀ w : D, (G.walkupE w).Jordan) {x t y : D}
    {p : List D} (hd : G.MoebiusData x (y :: p) t) : G.face x = y := by
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  rcases (List.isChain_cons_cons.mp hchain).1 with hxy | hxy
  swap
  · exact hxy
  -- `x = node y`: delete `x`
  exfalso
  have hxnotmem : x ∉ y :: p := (List.nodup_cons.mp hnodup).1
  have hne : ∀ w ∈ y :: p, w ≠ x := fun w hw hc => hxnotmem (hc ▸ hw)
  have hneP : ∀ w ∈ p, w ≠ x := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  have hy : y ≠ x := hne y List.mem_cons_self
  have ht : t ≠ x := hne t hmem2.mem_left
  have hlast : G.node t = p.getLastD y := by rw [hnt, getLastD_cons]
  have hntx : G.node t ≠ x := by
    rw [hlast]
    exact hne _ (getLastD_mem_cons y p)
  have hnodey : G.node y = x := hxy.symm
  have hnxx : G.node x ≠ x := by
    have h := skipFun_ne G.node x hy
    simpa only [skipFun, ite_eq_left hnodey] using h
  have hnodev : (G.walkupE x).node (⟨y, hy⟩ : Walkup G x) = ⟨G.node x, hnxx⟩ :=
    Subtype.ext (by simp only [walkupE_node, skip_val, skipFun, ite_eq_left hnodey])
  -- `t` cannot be the head of the tail, since `node t` lies on the tail
  have htmem : Mem2 p t (G.node x) := by
    rcases Mem2.cons_iff.mp hmem2 with ⟨rfl, -⟩ | h
    · exact absurd (hnodey.symm.trans hlast ▸ hne _ (getLastD_mem_cons t p)) (by simp)
    · exact h
  set q : List (Walkup G x) := p.attachWith (· ≠ x) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmap : ((⟨y, hy⟩ : Walkup G x) :: q).map Subtype.val = y :: p := by
    rw [List.map_cons, hmapq]
  refine hJE x _ ((G.walkupE x).moebiusPath_of_data (x := ⟨y, hy⟩) (p := q)
    (t := ⟨t, ht⟩) ⟨?_, ?_, ?_, ?_⟩)
  · exact List.Nodup.of_map Subtype.val (by rw [hmap]; exact (List.nodup_cons.mp hnodup).2)
  · exact isChain_clink_walkupE G x (by rw [hmap]; exact (List.isChain_cons_cons.mp hchain).2)
  · refine Subtype.ext ?_
    rw [walkupE_node, skip_val_of_ne (u := (⟨t, ht⟩ : Walkup G x)) hntx]
    have hgl := getLastD_map (Subtype.val (p := fun w : D => w ≠ x)) q ⟨y, hy⟩
    rw [hmapq] at hgl
    rw [hlast, hgl]
  · rw [hnodev]
    exact (Mem2.map_iff (f := (Subtype.val : Walkup G x → D)) Subtype.val_injective).mp
      (by rw [hmapq]; exact htmem)

/-! ### A minimal counterexample is longer than two darts -/

theorem not_moebiusData_singleton {x t y : D} (hd : G.MoebiusData x [y] t) : False := by
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hnt' : G.node t = y := by rw [getLastD_cons] at hnt; exact hnt
  rcases Mem2.cons_iff.mp hmem2 with ⟨rfl, hb | hb⟩ | h
  · have hxt : x ≠ t := fun hc => (List.nodup_cons.mp hnodup).1 (by simp [hc])
    exact hxt (G.node.injective (hb.trans hnt'.symm))
  · simp at hb
  · obtain ⟨p₁, p₂, hp, -⟩ := h
    simp at hp

/-! ### The second link of a minimal counterexample is an F-link

A reverse N-link in second position can be cut away with the F-transform,
which links the first dart directly to the third.
-/

theorem face_snd_of_moebiusData (hJF : ∀ w : D, (G.walkupF w).Jordan) {x t y z : D}
    {p : List D} (hd : G.MoebiusData x (y :: z :: p) t) (hfx : G.face x = y) :
    G.face y = z := by
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hchain1 := List.isChain_cons_cons.mp hchain
  have hchain2 := List.isChain_cons_cons.mp hchain1.2
  rcases hchain2.1 with hyz | hyz
  swap
  · exact hyz
  exfalso
  -- `y = node z`: delete `y` with the F-transform
  have hnd2 : (y :: z :: p).Nodup := (List.nodup_cons.mp hnodup).2
  have hynotin : y ∉ z :: p := (List.nodup_cons.mp hnd2).1
  have hxnotin : x ∉ y :: z :: p := (List.nodup_cons.mp hnodup).1
  have hxy : x ≠ y := fun hc => hxnotin (hc ▸ List.mem_cons_self)
  have hne : ∀ w ∈ z :: p, w ≠ y := fun w hw hc => hynotin (hc ▸ hw)
  have hzy : z ≠ y := hne z List.mem_cons_self
  have hneP : ∀ w ∈ p, w ≠ y := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  have hxz : x ≠ z := fun hc =>
    hxnotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hnodez : G.node z = y := hyz.symm
  have hnodey : G.node y ≠ y := fun hc => hzy (G.node.injective (hnodez.trans hc.symm))
  have hen : G.edge (G.node y) = x := G.face.injective ((G.nodeK y).trans hfx.symm)
  have hfey : G.face (G.edge y) = z := G.node.injective ((G.edgeK y).trans hnodez.symm)
  have hlast : G.node t = p.getLastD z := by rw [hnt, getLastD_cons, getLastD_cons]
  have hnxy : G.node x ≠ y := fun hc => hxz (G.node.injective (hc.trans hnodez.symm))
  -- the lifted path
  set q : List (Walkup G y) := p.attachWith (· ≠ y) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmapl : ((⟨x, hxy⟩ : Walkup G y) :: (⟨z, hzy⟩ : Walkup G y) :: q).map Subtype.val
      = x :: z :: p := by rw [List.map_cons, List.map_cons, hmapq]
  have hnodupl : ((⟨x, hxy⟩ : Walkup G y) :: (⟨z, hzy⟩ : Walkup G y) :: q).Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    rw [hmapl]
    exact List.nodup_cons.mpr ⟨fun hc => hxnotin (List.mem_cons_of_mem _ hc),
      (List.nodup_cons.mp hnd2).2⟩
  have hchainl : List.IsChain (G.walkupF y).Clink
      ((⟨x, hxy⟩ : Walkup G y) :: (⟨z, hzy⟩ : Walkup G y) :: q) := by
    refine List.IsChain.cons_cons (Or.inr ?_) ?_
    · exact walkupF_face_eq_jump G y hnodey hnodez (by rw [hen]; exact hxy) hen.symm
    · refine isChain_clink_walkupF G y ?_ (by rw [List.map_cons, hmapq]; exact hchain2.2)
      intro u hu
      rw [hfey]
      have hup : u.val ∈ p := by rw [← hmapq]; exact List.mem_map_of_mem hu
      exact fun hc => (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1 (hc ▸ hup)
  have hnodex : (G.walkupF y).node (⟨x, hxy⟩ : Walkup G y) = ⟨G.node x, hnxy⟩ :=
    Subtype.ext (skip_val_of_ne (u := (⟨x, hxy⟩ : Walkup G y)) hnxy)
  have hlastl : (((⟨z, hzy⟩ : Walkup G y) :: q).getLastD (⟨x, hxy⟩ : Walkup G y)).val
      = p.getLastD z := by
    have hgl := getLastD_map (Subtype.val (p := fun w : D => w ≠ y))
      ((⟨z, hzy⟩ : Walkup G y) :: q) ⟨x, hxy⟩
    rw [List.map_cons, hmapq] at hgl
    rw [← hgl, getLastD_cons]
  rcases eq_or_ne t y with rfl | hty
  -- the crossing dart is the deleted one: it is replaced by the third dart
  · refine hJF t _ ((G.walkupF t).moebiusPath_of_data (x := ⟨x, hxy⟩)
      (p := (⟨z, hzy⟩ : Walkup G t) :: q) (t := ⟨z, hzy⟩) ⟨hnodupl, hchainl, ?_, ?_⟩)
    · refine Subtype.ext ?_
      rw [walkupF_node, skip_val_of_eq (u := (⟨z, hzy⟩ : Walkup G t)) hnodez, hlastl, hlast]
    · rw [hnodex]
      refine (Mem2.map_iff (f := (Subtype.val : Walkup G t → D)) Subtype.val_injective).mp ?_
      rw [List.map_cons, hmapq]
      rcases Mem2.cons_iff.mp hmem2 with ⟨-, hb | hb⟩ | h
      · exact absurd hb hnxy
      · exact Mem2.cons_self (List.mem_cons.mp hb)
      · exact absurd (hne _ h.mem_left) (by simp)
  -- the crossing dart survives the deletion
  · have ht : t ≠ y := hty
    have hnty : G.node t ≠ y := by
      rw [hlast]
      exact hne _ (getLastD_mem_cons z p)
    refine hJF y _ ((G.walkupF y).moebiusPath_of_data (x := ⟨x, hxy⟩)
      (p := (⟨z, hzy⟩ : Walkup G y) :: q) (t := ⟨t, ht⟩) ⟨hnodupl, hchainl, ?_, ?_⟩)
    · refine Subtype.ext ?_
      rw [walkupF_node, skip_val_of_ne (u := (⟨t, ht⟩ : Walkup G y)) hnty, hlastl, hlast]
    · rw [hnodex]
      refine (Mem2.map_iff (f := (Subtype.val : Walkup G y → D)) Subtype.val_injective).mp ?_
      rw [List.map_cons, hmapq]
      rcases Mem2.cons_iff.mp hmem2 with ⟨hc, -⟩ | h
      · exact absurd hc hty
      · exact h

/-! ### The crossing dart of a minimal counterexample is the second one -/

theorem crossing_eq_of_moebiusData (hJE : ∀ w : D, (G.walkupE w).Jordan) {x t y z : D}
    {p : List D} (hd : G.MoebiusData x (y :: z :: p) t) (hfx : G.face x = y)
    (hfy : G.face y = z) : t = y := by
  by_contra hty
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hchain1 := List.isChain_cons_cons.mp hchain
  have hchain2 := List.isChain_cons_cons.mp hchain1.2
  have hnd2 : (y :: z :: p).Nodup := (List.nodup_cons.mp hnodup).2
  have hynotin : y ∉ z :: p := (List.nodup_cons.mp hnd2).1
  have hxnotin : x ∉ y :: z :: p := (List.nodup_cons.mp hnodup).1
  have hxy : x ≠ y := fun hc => hxnotin (hc ▸ List.mem_cons_self)
  have hne : ∀ w ∈ z :: p, w ≠ y := fun w hw hc => hynotin (hc ▸ hw)
  have hzy : z ≠ y := hne z List.mem_cons_self
  have hneP : ∀ w ∈ p, w ≠ y := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  have hlast : G.node t = p.getLastD z := by rw [hnt, getLastD_cons, getLastD_cons]
  have hnty : G.node t ≠ y := by
    rw [hlast]
    exact hne _ (getLastD_mem_cons z p)
  -- with `t` away from the deleted dart, the crossing N-link survives
  have hmem2' : Mem2 (z :: p) t (G.node x) := by
    rcases Mem2.cons_iff.mp hmem2 with ⟨hc, -⟩ | h
    · exact absurd hc hty
    · exact h
  have hnxy : G.node x ≠ y := hne _ hmem2'.mem_right
  set q : List (Walkup G y) := p.attachWith (· ≠ y) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmapl : ((⟨x, hxy⟩ : Walkup G y) :: (⟨z, hzy⟩ : Walkup G y) :: q).map Subtype.val
      = x :: z :: p := by rw [List.map_cons, List.map_cons, hmapq]
  refine hJE y _ ((G.walkupE y).moebiusPath_of_data (x := ⟨x, hxy⟩)
    (p := (⟨z, hzy⟩ : Walkup G y) :: q) (t := ⟨t, hty⟩) ⟨?_, ?_, ?_, ?_⟩)
  · refine List.Nodup.of_map Subtype.val ?_
    rw [hmapl]
    exact List.nodup_cons.mpr ⟨fun hc => hxnotin (List.mem_cons_of_mem _ hc),
      (List.nodup_cons.mp hnd2).2⟩
  · refine List.IsChain.cons_cons (Or.inr ?_) ?_
    · exact Subtype.ext (by
        rw [walkupE_face, skip_val_of_eq (u := (⟨x, hxy⟩ : Walkup G y)) hfx, hfy])
    · exact isChain_clink_walkupE G y (by rw [List.map_cons, hmapq]; exact hchain2.2)
  · refine Subtype.ext ?_
    have hgl := getLastD_map (Subtype.val (p := fun w : D => w ≠ y))
      ((⟨z, hzy⟩ : Walkup G y) :: q) ⟨x, hxy⟩
    rw [List.map_cons, hmapq] at hgl
    rw [walkupE_node, skip_val_of_ne (u := (⟨t, hty⟩ : Walkup G y)) hnty, ← hgl,
      getLastD_cons, hlast]
  · have hnodex : (G.walkupE y).node (⟨x, hxy⟩ : Walkup G y) = ⟨G.node x, hnxy⟩ :=
      Subtype.ext (skip_val_of_ne (u := (⟨x, hxy⟩ : Walkup G y)) hnxy)
    rw [hnodex]
    refine (Mem2.map_iff (f := (Subtype.val : Walkup G y → D)) Subtype.val_injective).mp ?_
    rw [List.map_cons, hmapq]
    exact hmem2'

/-! ### The head of a minimal counterexample carries a crossing N-link -/

theorem node_head_of_moebiusData (hJN : ∀ w : D, (G.walkupN w).Jordan) {x y z : D}
    {p : List D} (hd : G.MoebiusData x (y :: z :: p) y) (hfx : G.face x = y)
    (hfy : G.face y = z) : G.node x = y := by
  by_contra hnxy
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hchain1 := List.isChain_cons_cons.mp hchain
  have hchain2 := List.isChain_cons_cons.mp hchain1.2
  have hnd2 : (y :: z :: p).Nodup := (List.nodup_cons.mp hnodup).2
  have hynotin : y ∉ z :: p := (List.nodup_cons.mp hnd2).1
  have hxnotin : x ∉ y :: z :: p := (List.nodup_cons.mp hnodup).1
  have hxy : x ≠ y := fun hc => hxnotin (hc ▸ List.mem_cons_self)
  have hne : ∀ w ∈ z :: p, w ≠ y := fun w hw hc => hynotin (hc ▸ hw)
  have hzy : z ≠ y := hne z List.mem_cons_self
  have hneP : ∀ w ∈ p, w ≠ y := fun w hw => hne w (List.mem_cons_of_mem _ hw)
  have hxz : x ≠ z := fun hc =>
    hxnotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hlast : G.node y = p.getLastD z := by rw [hnt, getLastD_cons, getLastD_cons]
  have hlastne : p.getLastD z ≠ y := hne _ (getLastD_mem_cons z p)
  -- the node image of the third dart jumps over the deleted one
  have hfel : G.face (G.edge (p.getLastD z)) = y := by rw [← hlast]; exact G.nodeK y
  have hel : G.edge (p.getLastD z) ≠ y := by
    intro hc
    rw [hc, hfy] at hfel
    exact hzy hfel
  have hnodet : (G.walkupN y).node (⟨z, hzy⟩ : Walkup G y)
      = ⟨p.getLastD z, hlastne⟩ :=
    walkupN_node_eq_jump G y (u := ⟨p.getLastD z, hlastne⟩) (v := ⟨z, hzy⟩) hel hfel hfy.symm
  -- and that of the head does not
  have henx : G.edge (G.node x) ≠ y := by
    intro hc
    have h0 : G.face (G.edge (G.node x)) = x := G.nodeK x
    rw [hc, hfy] at h0
    exact hxz h0.symm
  have hnodex : (G.walkupN y).node (⟨x, hxy⟩ : Walkup G y) = ⟨G.node x, hnxy⟩ :=
    walkupN_node_eq_of G y (u := ⟨x, hxy⟩) hnxy henx
  set q : List (Walkup G y) := p.attachWith (· ≠ y) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmapl : ((⟨x, hxy⟩ : Walkup G y) :: (⟨z, hzy⟩ : Walkup G y) :: q).map Subtype.val
      = x :: z :: p := by rw [List.map_cons, List.map_cons, hmapq]
  refine hJN y _ ((G.walkupN y).moebiusPath_of_data (x := ⟨x, hxy⟩)
    (p := (⟨z, hzy⟩ : Walkup G y) :: q) (t := ⟨z, hzy⟩) ⟨?_, ?_, ?_, ?_⟩)
  · refine List.Nodup.of_map Subtype.val ?_
    rw [hmapl]
    exact List.nodup_cons.mpr ⟨fun hc => hxnotin (List.mem_cons_of_mem _ hc),
      (List.nodup_cons.mp hnd2).2⟩
  · refine List.IsChain.cons_cons (Or.inr ?_) ?_
    · exact Subtype.ext (by
        rw [walkupN_face, skip_val_of_eq (u := (⟨x, hxy⟩ : Walkup G y)) hfx, hfy])
    · refine isChain_clink_walkupN G y ?_ (by rw [List.map_cons, hmapq]; exact hchain2.2)
      intro u hu
      rw [hfy]
      have hup : u.val ∈ p := by rw [← hmapq]; exact List.mem_map_of_mem hu
      exact fun hc => (List.nodup_cons.mp (List.nodup_cons.mp hnd2).2).1 (hc ▸ hup)
  · refine Subtype.ext ?_
    have hgl := getLastD_map (Subtype.val (p := fun w : D => w ≠ y))
      ((⟨z, hzy⟩ : Walkup G y) :: q) ⟨x, hxy⟩
    rw [List.map_cons, hmapq] at hgl
    rw [hnodet, ← hgl, getLastD_cons]
  · rw [hnodex]
    refine (Mem2.map_iff (f := (Subtype.val : Walkup G y → D)) Subtype.val_injective).mp ?_
    rw [List.map_cons, hmapq]
    rcases Mem2.cons_iff.mp hmem2 with ⟨-, hb | hb⟩ | h
    · exact absurd hb hnxy
    · exact Mem2.cons_self (List.mem_cons.mp hb)
    · exact absurd (hne _ h.mem_left) (by simp)

/-! ### A minimal counterexample has at most three darts

Once the head of the path carries the crossing N-link and the first two links
are F-links, the third dart can be deleted: with an F-transform if it is left
by a reverse N-link, with an E-transform otherwise.
-/

theorem node_fourth_of_moebiusData (hJE : ∀ w : D, (G.walkupE w).Jordan) {x y z w : D}
    {p : List D} (hd : G.MoebiusData x (y :: z :: w :: p) y) (hfy : G.face y = z)
    (hnx : G.node x = y) : G.node w = z := by
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hchain1 := List.isChain_cons_cons.mp hchain
  have hchain2 := List.isChain_cons_cons.mp hchain1.2
  have hchain3 := List.isChain_cons_cons.mp hchain2.2
  rcases hchain3.1 with hzw | hzw
  · exact hzw.symm
  exfalso
  -- `face z = w`: delete `z` with the E-transform
  have hnd2 : (y :: z :: w :: p).Nodup := (List.nodup_cons.mp hnodup).2
  have hnd3 : (z :: w :: p).Nodup := (List.nodup_cons.mp hnd2).2
  have hznotin : z ∉ w :: p := (List.nodup_cons.mp hnd3).1
  have hxnotin : x ∉ y :: z :: w :: p := (List.nodup_cons.mp hnodup).1
  have hynotin : y ∉ z :: w :: p := (List.nodup_cons.mp hnd2).1
  have hxz : x ≠ z := fun hc =>
    hxnotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hyz : y ≠ z := fun hc => hynotin (hc ▸ List.mem_cons_self)
  have hne : ∀ v ∈ w :: p, v ≠ z := fun v hv hc => hznotin (hc ▸ hv)
  have hwz : w ≠ z := hne w List.mem_cons_self
  have hneP : ∀ v ∈ p, v ≠ z := fun v hv => hne v (List.mem_cons_of_mem _ hv)
  have hlast : G.node y = p.getLastD w := by
    rw [hnt, getLastD_cons, getLastD_cons, getLastD_cons]
  have hnyz : G.node y ≠ z := by
    rw [hlast]
    exact hne _ (getLastD_mem_cons w p)
  have hnxz : G.node x ≠ z := by rw [hnx]; exact hyz
  set q : List (Walkup G z) := p.attachWith (· ≠ z) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmapl : ((⟨x, hxz⟩ : Walkup G z) :: (⟨y, hyz⟩ : Walkup G z) ::
      (⟨w, hwz⟩ : Walkup G z) :: q).map Subtype.val = x :: y :: w :: p := by
    rw [List.map_cons, List.map_cons, List.map_cons, hmapq]
  refine hJE z _ ((G.walkupE z).moebiusPath_of_data (x := ⟨x, hxz⟩)
    (p := (⟨y, hyz⟩ : Walkup G z) :: (⟨w, hwz⟩ : Walkup G z) :: q)
    (t := ⟨y, hyz⟩) ⟨?_, ?_, ?_, ?_⟩)
  · refine List.Nodup.of_map Subtype.val ?_
    rw [hmapl]
    refine List.nodup_cons.mpr ⟨fun hc => hxnotin ?_, List.nodup_cons.mpr
      ⟨fun hc => hynotin (List.mem_cons_of_mem _ hc), (List.nodup_cons.mp hnd3).2⟩⟩
    rcases List.mem_cons.mp hc with hc | hc
    · exact hc ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
  · refine List.IsChain.cons_cons (clink_walkupE_of_clink G z hchain1.1)
      (List.IsChain.cons_cons (Or.inr ?_) ?_)
    · exact Subtype.ext (by
        rw [walkupE_face, skip_val_of_eq (u := (⟨y, hyz⟩ : Walkup G z)) hfy, hzw])
    · exact isChain_clink_walkupE G z (by rw [List.map_cons, hmapq]; exact hchain3.2)
  · refine Subtype.ext ?_
    have hgl := getLastD_map (Subtype.val (p := fun v : D => v ≠ z))
      ((⟨y, hyz⟩ : Walkup G z) :: (⟨w, hwz⟩ : Walkup G z) :: q) ⟨x, hxz⟩
    rw [List.map_cons, List.map_cons, hmapq] at hgl
    rw [walkupE_node, skip_val_of_ne (u := (⟨y, hyz⟩ : Walkup G z)) hnyz, ← hgl,
      getLastD_cons, getLastD_cons, hlast]
  · have hnodex : (G.walkupE z).node (⟨x, hxz⟩ : Walkup G z) = ⟨y, hyz⟩ :=
      Subtype.ext (by rw [walkupE_node, skip_val_of_ne (u := (⟨x, hxz⟩ : Walkup G z)) hnxz, hnx])
    rw [hnodex]
    exact Mem2.cons_self (Or.inl rfl)

theorem not_moebiusData_four (hJF : ∀ v : D, (G.walkupF v).Jordan) {x y z w : D}
    {p : List D} (hd : G.MoebiusData x (y :: z :: w :: p) y) (hfy : G.face y = z)
    (hnx : G.node x = y) (hnw : G.node w = z) : False := by
  obtain ⟨hnodup, hchain, hnt, hmem2⟩ := hd
  have hchain1 := List.isChain_cons_cons.mp hchain
  have hchain2 := List.isChain_cons_cons.mp hchain1.2
  have hchain3 := List.isChain_cons_cons.mp hchain2.2
  have hnd2 : (y :: z :: w :: p).Nodup := (List.nodup_cons.mp hnodup).2
  have hnd3 : (z :: w :: p).Nodup := (List.nodup_cons.mp hnd2).2
  have hznotin : z ∉ w :: p := (List.nodup_cons.mp hnd3).1
  have hxnotin : x ∉ y :: z :: w :: p := (List.nodup_cons.mp hnodup).1
  have hynotin : y ∉ z :: w :: p := (List.nodup_cons.mp hnd2).1
  have hxz : x ≠ z := fun hc =>
    hxnotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hyz : y ≠ z := fun hc => hynotin (hc ▸ List.mem_cons_self)
  have hne : ∀ v ∈ w :: p, v ≠ z := fun v hv hc => hznotin (hc ▸ hv)
  have hwz : w ≠ z := hne w List.mem_cons_self
  have hneP : ∀ v ∈ p, v ≠ z := fun v hv => hne v (List.mem_cons_of_mem _ hv)
  have hyw : y ≠ w := fun hc => hynotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hlast : G.node y = p.getLastD w := by
    rw [hnt, getLastD_cons, getLastD_cons, getLastD_cons]
  have hnyz : G.node y ≠ z := by
    rw [hlast]
    exact hne _ (getLastD_mem_cons w p)
  have hnxz : G.node x ≠ z := by rw [hnx]; exact hyz
  -- the exceptional darts of the F-transform at `z`
  have hnodez : G.node z ≠ z := fun hc => hwz (G.node.injective (hnw.trans hc.symm))
  have hen : G.edge (G.node z) = y := G.face.injective ((G.nodeK z).trans hfy.symm)
  have hfez : G.face (G.edge z) = w := G.node.injective ((G.edgeK z).trans hnw.symm)
  set q : List (Walkup G z) := p.attachWith (· ≠ z) hneP with hq
  have hmapq : q.map Subtype.val = p := List.attachWith_map_subtype_val hneP
  have hmapl : ((⟨x, hxz⟩ : Walkup G z) :: (⟨y, hyz⟩ : Walkup G z) ::
      (⟨w, hwz⟩ : Walkup G z) :: q).map Subtype.val = x :: y :: w :: p := by
    rw [List.map_cons, List.map_cons, List.map_cons, hmapq]
  refine hJF z _ ((G.walkupF z).moebiusPath_of_data (x := ⟨x, hxz⟩)
    (p := (⟨y, hyz⟩ : Walkup G z) :: (⟨w, hwz⟩ : Walkup G z) :: q)
    (t := ⟨y, hyz⟩) ⟨?_, ?_, ?_, ?_⟩)
  · refine List.Nodup.of_map Subtype.val ?_
    rw [hmapl]
    refine List.nodup_cons.mpr ⟨fun hc => hxnotin ?_, List.nodup_cons.mpr
      ⟨fun hc => hynotin (List.mem_cons_of_mem _ hc), (List.nodup_cons.mp hnd3).2⟩⟩
    rcases List.mem_cons.mp hc with hc | hc
    · exact hc ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
  · refine List.IsChain.cons_cons (clink_walkupF_of_clink G z ?_ hchain1.1)
      (List.IsChain.cons_cons ?_ ?_)
    · rw [hfez]; exact hyw
    · exact Or.inr (walkupF_face_eq_jump G z hnodez hnw (by rw [hen]; exact hyz) hen.symm)
    · refine isChain_clink_walkupF G z ?_ (by rw [List.map_cons, hmapq]; exact hchain3.2)
      intro u hu
      rw [hfez]
      have hup : u.val ∈ p := by rw [← hmapq]; exact List.mem_map_of_mem hu
      exact fun hc => (List.nodup_cons.mp (List.nodup_cons.mp hnd3).2).1 (hc ▸ hup)
  · refine Subtype.ext ?_
    have hgl := getLastD_map (Subtype.val (p := fun v : D => v ≠ z))
      ((⟨y, hyz⟩ : Walkup G z) :: (⟨w, hwz⟩ : Walkup G z) :: q) ⟨x, hxz⟩
    rw [List.map_cons, List.map_cons, hmapq] at hgl
    rw [walkupF_node, skip_val_of_ne (u := (⟨y, hyz⟩ : Walkup G z)) hnyz, ← hgl,
      getLastD_cons, getLastD_cons, hlast]
  · have hnodex : (G.walkupF z).node (⟨x, hxz⟩ : Walkup G z) = ⟨y, hyz⟩ :=
      Subtype.ext (by rw [walkupF_node, skip_val_of_ne (u := (⟨x, hxz⟩ : Walkup G z)) hnxz, hnx])
    rw [hnodex]
    exact Mem2.cons_self (Or.inl rfl)

/-! ### The three-dart case

A Moebius path of three darts forces all three permutations to be the same
three-cycle, and the Euler formula then gives genus one.
-/

private theorem cycleCount_eq_one_of_three [Fintype D] {f : Perm D} {x y z : D}
    (hmem : ∀ v : D, v = x ∨ v = y ∨ v = z) (hfx : f x = y) (hfy : f y = z) :
    cycleCount f = 1 := by
  have hxy : f.SameCycle x y := ⟨1, by simpa using hfx⟩
  have hyz : f.SameCycle y z := ⟨1, by simpa using hfy⟩
  have hsc : ∀ v : D, f.SameCycle x v := by
    intro v
    rcases hmem v with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl f v
    · exact hxy
    · exact hxy.trans hyz
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨Quotient.mk _ x⟩⟩
  refine Quotient.inductionOn₂ a b fun u v => Quotient.sound ?_
  exact (hsc u).symm.trans (hsc v)

private theorem compCount_eq_one_of_three [Fintype D] {x y z : D}
    (hmem : ∀ v : D, v = x ∨ v = y ∨ v = z) (hfx : G.face x = y) (hfy : G.face y = z) :
    G.compCount = 1 := by
  have hxy : Relation.EqvGen G.GLink x y := Relation.EqvGen.rel _ _ (hfx ▸ G.glink_face x)
  have hyz : Relation.EqvGen G.GLink y z := Relation.EqvGen.rel _ _ (hfy ▸ G.glink_face y)
  have hsc : ∀ v : D, Relation.EqvGen G.GLink x v := by
    intro v
    rcases hmem v with rfl | rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact hxy
    · exact Relation.EqvGen.trans _ _ _ hxy hyz
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨Quotient.mk _ x⟩⟩
  refine Quotient.inductionOn₂ a b fun u v => Quotient.sound ?_
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hsc u)) (hsc v)

private theorem card_eq_three [Fintype D] {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hmem : ∀ v : D, v = x ∨ v = y ∨ v = z) : Nat.card D = 3 := by
  classical
  have huniv : (Finset.univ : Finset D) = {x, y, z} := by
    ext v
    simpa using hmem v
  rw [Nat.card_eq_fintype_card, Fintype.card, huniv]
  simp [hxy, hxz, hyz]

private theorem not_planar_of_three [Fintype D] {x y z : D} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hmem : ∀ v : D, v = x ∨ v = y ∨ v = z) (hfx : G.face x = y)
    (hfy : G.face y = z) (hnx : G.node x = y) (hny : G.node y = z) : ¬ G.Planar := by
  -- the node and face three-cycles close up
  have hnz : G.node z = x := by
    rcases hmem (G.node z) with h | h | h
    · exact h
    · exact absurd (G.node.injective (h.trans hnx.symm)) hxz.symm
    · exact absurd (G.node.injective (h.trans hny.symm)) hyz.symm
  have hfz : G.face z = x := by
    rcases hmem (G.face z) with h | h | h
    · exact h
    · exact absurd (G.face.injective (h.trans hfx.symm)) hxz.symm
    · exact absurd (G.face.injective (h.trans hfy.symm)) hyz.symm
  -- hence so does the edge one
  have hex : G.edge x = y := by
    have h1 : G.node (G.face (G.edge x)) = x := G.edgeK x
    have h2 : G.node (G.face y) = x := by rw [hfy, hnz]
    exact G.face.injective (G.node.injective (h1.trans h2.symm))
  have hey : G.edge y = z := by
    have h1 : G.node (G.face (G.edge y)) = y := G.edgeK y
    have h2 : G.node (G.face z) = y := by rw [hfz, hnx]
    exact G.face.injective (G.node.injective (h1.trans h2.symm))
  simp only [Planar, genus, EulerLhs, EulerRhs,
    compCount_eq_one_of_three G hmem hfx hfy,
    cycleCount_eq_one_of_three hmem hex hey,
    cycleCount_eq_one_of_three hmem hnx hny,
    cycleCount_eq_one_of_three hmem hfx hfy,
    card_eq_three hxy hxz hyz hmem]
  decide

/-! ### Planarity implies the Jordan curve property -/

omit [DecidableEq D] in
private theorem jordan_of_card_le : ∀ (n : ℕ) {D : Type*} [DecidableEq D] [Fintype D]
    (G : Hypermap D), Fintype.card D ≤ n → G.Planar → G.Jordan := by
  intro n
  induction n with
  | zero =>
    intro D _ _ G hn _ q hq
    have hD : IsEmpty D := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hn)
    match q with
    | [] => exact hq
    | x :: p => exact isEmptyElim x
  | succ n ih =>
    intro D _ _ G hn hplanar q hq
    have hlt : ∀ w : D, Fintype.card (Walkup G w) ≤ n := by
      intro w
      have hcw := card_walkup G w
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcw
      omega
    have hJE : ∀ w : D, (G.walkupE w).Jordan := fun w =>
      ih (G.walkupE w) (hlt w) (planar_walkupE G w hplanar)
    have hJN : ∀ w : D, (G.walkupN w).Jordan := fun w =>
      ih (G.walkupN w) (hlt w) (planar_walkupN G w hplanar)
    have hJF : ∀ w : D, (G.walkupF w).Jordan := fun w =>
      ih (G.walkupF w) (hlt w) (planar_walkupF G w hplanar)
    match q, hq with
    | [], hq => exact hq
    | x :: p, hq =>
      obtain ⟨hnodup, hchain, hmem2⟩ := hq
      have hd : G.MoebiusData x p (G.node⁻¹ (p.getLastD x)) :=
        ⟨hnodup, hchain, by simp, hmem2⟩
      clear hmem2 hchain hnodup
      match p, hd with
      | [], hd =>
        obtain ⟨-, -, -, hm⟩ := hd
        obtain ⟨p₁, p₂, hp, -⟩ := hm
        simp at hp
      | [y], hd => exact not_moebiusData_singleton G hd
      | y :: z :: p', hd =>
        have hfx := face_head_of_moebiusData G hJE hd
        have hfy := face_snd_of_moebiusData G hJF hd hfx
        have hty := crossing_eq_of_moebiusData G hJE hd hfx hfy
        rw [hty] at hd
        have hnx := node_head_of_moebiusData G hJN hd hfx hfy
        match p', hd with
        | [], hd =>
          have hmemall := mem_of_moebiusData G hJE hd
          obtain ⟨hnodup, -, hnt, -⟩ := hd
          have hny : G.node y = z := by
            rw [hnt, getLastD_cons, getLastD_cons]
            rfl
          have hxnotin : x ∉ [y, z] := (List.nodup_cons.mp hnodup).1
          have hxy : x ≠ y := fun hc => hxnotin (hc ▸ List.mem_cons_self)
          have hxz : x ≠ z := fun hc =>
            hxnotin (by rw [hc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          have hyz : y ≠ z := fun hc =>
            (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1 (hc ▸ List.mem_cons_self)
          refine not_planar_of_three G hxy hxz hyz ?_ hfx hfy hnx hny hplanar
          intro v
          have hv := hmemall v
          rcases List.mem_cons.mp hv with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (List.mem_singleton.mp h))
        | w :: p'', hd =>
          have hnw := node_fourth_of_moebiusData G hJE hd hfy hnx
          exact not_moebiusData_four G hJF hd hfy hnx hnw

omit [DecidableEq D] in
/-- A hypermap of genus zero has no Moebius path: the Jordan curve property,
the reference's `planar_Jordan`. -/
theorem Planar.jordan [Finite D] (h : G.Planar) : G.Jordan := by
  classical
  have := Fintype.ofFinite D
  exact jordan_of_card_le (Fintype.card D) G le_rfl h

end Hypermap

end FourColor

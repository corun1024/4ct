import FourColor.Geometry
import FourColor.Patch

/-!
# Sewing two maps along a common border

Two hypermaps can be glued along a border: an E-cycle of the first and an
N-cycle of the second, matched dart for dart.  The result is a hypermap whose
darts are those of the first together with those of the second off its border,
and it exhibits the two as a patch of the glued map.

The matching is taken as data (`SewMatch`) rather than computed from the two
border lists by index, which is how the reference does it: all its index
bookkeeping is then replaced by the two inverse laws and the single
compatibility law `node_toRest`.

## Main definitions

* `SewMatch` — a matching of the two borders.
* `SewDart` — the darts of the sewn map.
* `SewMatch.sewd`, `SewMatch.sewr` — the two injections.
* `SewMatch.sewMap` — the sewn hypermap.
-/

namespace FourColor

open Equiv Equiv.Perm

variable {Dd Dr : Type*}

/-- A matching of the two borders along which two maps are sewn: inverse
bijections between an `edge`-closed set of the first map and a `node`-closed set
of the second, taking the first map's `node ∘ face` to the second's `node`. -/
structure SewMatch (Gd : Hypermap Dd) (Gr : Hypermap Dr) (bd : List Dd)
    (br : List Dr) where
  /-- The border dart of the second map matching one of the first. -/
  toRest : Dd → Dr
  /-- The border dart of the first map matching one of the second. -/
  toDisk : Dr → Dd
  /-- The first border is closed under `edge`. -/
  mem_edge : ∀ x : Dd, Gd.edge x ∈ bd ↔ x ∈ bd
  /-- The second border is closed under `node`. -/
  mem_node : ∀ y : Dr, Gr.node y ∈ br ↔ y ∈ br
  /-- The matching maps the first border into the second. -/
  toRest_mem : ∀ x ∈ bd, toRest x ∈ br
  /-- The matching maps the second border into the first. -/
  toDisk_mem : ∀ y ∈ br, toDisk y ∈ bd
  /-- The two directions are inverse on the first border. -/
  toDisk_toRest : ∀ x ∈ bd, toDisk (toRest x) = x
  /-- The two directions are inverse on the second border. -/
  toRest_toDisk : ∀ y ∈ br, toRest (toDisk y) = y
  /-- The matching turns the first map's contour step into the second's
  `node`. -/
  node_toRest : ∀ x ∈ bd, Gr.node (toRest x) = toRest (Gd.node (Gd.face x))

namespace SewMatch

variable {Gd : Hypermap Dd} {Gr : Hypermap Dr} {bd : List Dd} {br : List Dr}
  (m : SewMatch Gd Gr bd br)

/-- The matching turns the second map's contour step into the first's `edge`. -/
theorem edge_toDisk {y : Dr} (hy : y ∈ br) :
    Gd.edge (m.toDisk y) = m.toDisk (Gr.face (Gr.edge y)) := by
  set z := Gr.face (Gr.edge y) with hz
  have hnz : Gr.node z = y := Gr.edgeK y
  have hzb : z ∈ br := (m.mem_node z).mp (by rw [hnz]; exact hy)
  have hzd : m.toDisk z ∈ bd := m.toDisk_mem z hzb
  -- the matching law at the disk dart matching `z`
  have hstep := m.node_toRest _ hzd
  rw [m.toRest_toDisk z hzb, hnz] at hstep
  -- the dart it names is again on the border
  have hmem : Gd.node (Gd.face (m.toDisk z)) ∈ bd := by
    have h1 : Gd.edge (Gd.node (Gd.face (m.toDisk z))) = m.toDisk z := Gd.faceK _
    exact (m.mem_edge _).mp (by rw [h1]; exact hzd)
  have hy' : m.toDisk y = Gd.node (Gd.face (m.toDisk z)) := by
    rw [hstep, m.toDisk_toRest _ hmem]
  rw [hy', Gd.faceK]

/-! ### The sewn map -/

/-- The darts of a sewn map: those of the first map, and those of the second
off its border. -/
abbrev _root_.FourColor.SewDart (Dd : Type*) {Dr : Type*} (br : List Dr) : Type _ :=
  Dd ⊕ {y : Dr // y ∉ br}

variable [DecidableEq Dr]

/-- The image of a dart of the first map. -/
def sewd (x : Dd) : SewDart Dd br := Sum.inl x

/-- The image of a dart of the second map; border darts land in the first. -/
def sewr (y : Dr) : SewDart Dd br :=
  if h : y ∈ br then Sum.inl (m.toDisk y) else Sum.inr ⟨y, h⟩

@[simp] theorem sewr_of_mem {y : Dr} (hy : y ∈ br) :
    m.sewr y = Sum.inl (m.toDisk y) := by
  rw [sewr, dite_eq_left hy]

theorem sewr_of_not_mem {y : Dr} (hy : y ∉ br) :
    m.sewr y = Sum.inr ⟨y, hy⟩ := by
  rw [sewr, dite_eq_right hy]

theorem sewr_toRest {x : Dd} (hx : x ∈ bd) : m.sewr (m.toRest x) = Sum.inl x := by
  rw [m.sewr_of_mem (m.toRest_mem x hx), m.toDisk_toRest x hx]

variable [DecidableEq Dd]

/-- The `edge` map of the sewn map. -/
def sewEdge : SewDart Dd br → SewDart Dd br
  | Sum.inl x => if h : x ∈ bd then m.sewr (Gr.edge (m.toRest x)) else Sum.inl (Gd.edge x)
  | Sum.inr u => m.sewr (Gr.edge u.val)

/-- The `face` map of the sewn map, on a dart of the second map. -/
def sewFaceRest (y : Dr) : SewDart Dd br :=
  match m.sewr (Gr.face y) with
  | Sum.inl x => Sum.inl (Gd.face x)
  | Sum.inr u => Sum.inr u

/-- The `face` map of the sewn map. -/
def sewFace : SewDart Dd br → SewDart Dd br
  | Sum.inl x => if h : x ∈ bd then m.sewFaceRest (m.toRest x) else Sum.inl (Gd.face x)
  | Sum.inr u => m.sewFaceRest u.val

/-- The `node` map of the sewn map. -/
def sewNode : SewDart Dd br → SewDart Dd br
  | Sum.inl x => Sum.inl (Gd.node x)
  | Sum.inr u => m.sewr (Gr.node u.val)

/-- Both branches of the sewn `edge` are followed by the same `face` step. -/
theorem sewFace_sewr (y : Dr) : m.sewFace (m.sewr y) = m.sewFaceRest y := by
  by_cases hy : y ∈ br
  · rw [m.sewr_of_mem hy]
    show (if h : m.toDisk y ∈ bd then _ else _) = _
    rw [dite_eq_left (m.toDisk_mem y hy), m.toRest_toDisk y hy]
  · rw [m.sewr_of_not_mem hy]
    rfl

/-- The triangular identity for the sewn maps. -/
theorem sewCancel3 (w : SewDart Dd br) : m.sewNode (m.sewFace (m.sewEdge w)) = w := by
  match w with
  | Sum.inl x =>
    by_cases hx : x ∈ bd
    · -- a border dart: the step crosses into the second map and back
      show m.sewNode (m.sewFace (if h : x ∈ bd then _ else _)) = _
      rw [dite_eq_left hx, m.sewFace_sewr]
      set y := m.toRest x with hy
      have hyb : y ∈ br := m.toRest_mem x hx
      have hfe : Gr.face (Gr.edge y) ∈ br := by
        refine (m.mem_node _).mp ?_
        rw [Gr.edgeK]
        exact hyb
      have hkey : m.toDisk (Gr.face (Gr.edge y)) = Gd.edge x := by
        have h := m.edge_toDisk hyb
        rw [m.toDisk_toRest x hx] at h
        exact h.symm
      show m.sewNode (match m.sewr (Gr.face (Gr.edge y)) with
        | Sum.inl z => Sum.inl (Gd.face z)
        | Sum.inr u => Sum.inr u) = _
      rw [m.sewr_of_mem hfe, hkey]
      show Sum.inl (Gd.node (Gd.face (Gd.edge x))) = Sum.inl x
      rw [Gd.edgeK]
    · -- an interior dart: the step stays in the first map
      show m.sewNode (m.sewFace (if h : x ∈ bd then _ else _)) = _
      rw [dite_eq_right hx]
      have hex : Gd.edge x ∉ bd := fun hc => hx ((m.mem_edge x).mp hc)
      show m.sewNode (if h : Gd.edge x ∈ bd then _ else _) = _
      rw [dite_eq_right hex]
      show Sum.inl (Gd.node (Gd.face (Gd.edge x))) = Sum.inl x
      rw [Gd.edgeK]
  | Sum.inr u =>
    show m.sewNode (m.sewFace (m.sewr (Gr.edge u.val))) = _
    rw [m.sewFace_sewr]
    have hfe : Gr.face (Gr.edge u.val) ∉ br := by
      intro hc
      refine u.2 ?_
      have := (m.mem_node (Gr.face (Gr.edge u.val))).mpr hc
      rwa [Gr.edgeK] at this
    show m.sewNode (match m.sewr (Gr.face (Gr.edge u.val)) with
      | Sum.inl z => Sum.inl (Gd.face z)
      | Sum.inr v => Sum.inr v) = _
    rw [m.sewr_of_not_mem hfe]
    show m.sewr (Gr.node (Gr.face (Gr.edge u.val))) = _
    rw [Gr.edgeK, m.sewr_of_not_mem u.2]

theorem sewd_injective : Function.Injective (sewd (Dd := Dd) (br := br)) := by
  intro x y h
  exact Sum.inl_injective h

theorem sewr_injective : Function.Injective m.sewr := by
  intro y y' h
  by_cases hy : y ∈ br <;> by_cases hy' : y' ∈ br
  · rw [m.sewr_of_mem hy, m.sewr_of_mem hy'] at h
    have := Sum.inl_injective h
    rw [← m.toRest_toDisk y hy, ← m.toRest_toDisk y' hy', this]
  · rw [m.sewr_of_mem hy, m.sewr_of_not_mem hy'] at h
    exact absurd h (by simp)
  · rw [m.sewr_of_not_mem hy, m.sewr_of_mem hy'] at h
    exact absurd h (by simp)
  · rw [m.sewr_of_not_mem hy, m.sewr_of_not_mem hy'] at h
    exact congrArg Subtype.val (Sum.inr_injective h)

/-- The sewn hypermap. -/
noncomputable def sewMap [Finite Dd] [Finite Dr] : Hypermap (SewDart Dd br) :=
  Hypermap.ofCancel3 m.sewEdge m.sewNode m.sewFace m.sewCancel3

@[simp] theorem sewMap_edge [Finite Dd] [Finite Dr] (w : SewDart Dd br) :
    (m.sewMap).edge w = m.sewEdge w := rfl

@[simp] theorem sewMap_node [Finite Dd] [Finite Dr] (w : SewDart Dd br) :
    (m.sewMap).node w = m.sewNode w := rfl

@[simp] theorem sewMap_face [Finite Dd] [Finite Dr] (w : SewDart Dd br) :
    (m.sewMap).face w = m.sewFace w := rfl

/-! ### The sewing is a patch -/

/-- The sewn map is the glueing of the two maps along their borders: the
reference's `sew_map_patch`. -/
theorem sewMap_patch [Finite Dd] [Finite Dr]
    (hbd : Gd.Scycle (fun u v => v = Gd.edge u) bd)
    (hbr : IsCyclicChain (fun u v => v = Gr.node u) br) (hbrn : br.Nodup)
    (hring : br.map m.toDisk = bd.reverse) :
    Patch m.sewMap Gd Gr (sewd (br := br)) m.sewr bd br where
  injd := sewd_injective
  injr := m.sewr_injective
  scycle_d := hbd
  cycle_r := hbr
  nodup_r := hbrn
  ring := by
    have h1 : br.map m.sewr = br.map (fun y => sewd (br := br) (m.toDisk y)) :=
      List.map_congr_left fun y hy => m.sewr_of_mem hy
    rw [h1]
    have h2 : br.map (fun y => sewd (br := br) (m.toDisk y))
        = (br.map m.toDisk).map (sewd (br := br)) := by
      rw [List.map_map]
      rfl
    rw [h2, hring, List.map_reverse]
  range_r := by
    intro w
    match w with
    | Sum.inl x =>
      constructor
      · rintro ⟨y, hy⟩
        refine Or.inr ?_
        by_cases hyb : y ∈ br
        · rw [m.sewr_of_mem hyb] at hy
          have hx : m.toDisk y = x := Sum.inl_injective hy
          exact List.mem_map.mpr ⟨x, hx ▸ m.toDisk_mem y hyb, rfl⟩
        · rw [m.sewr_of_not_mem hyb] at hy
          exact absurd hy (by simp)
      · rintro (hc | hc)
        · exact absurd ⟨x, rfl⟩ hc
        · obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hc
          have hzx' : z = x := Sum.inl_injective hzx
          refine ⟨m.toRest x, ?_⟩
          rw [m.sewr_toRest (hzx' ▸ hz)]
    | Sum.inr u =>
      constructor
      · intro _
        refine Or.inl fun hc => ?_
        obtain ⟨x, hx⟩ := hc
        exact absurd hx (by simp [sewd])
      · intro _
        exact ⟨u.val, m.sewr_of_not_mem u.2⟩
  edge_d := by
    intro xd hxd
    show _ = m.sewEdge (Sum.inl xd)
    show _ = (if h : xd ∈ bd then _ else _)
    rw [dite_eq_right hxd]
    rfl
  node_d := fun _ => rfl
  edge_r := by
    intro xr
    show _ = m.sewEdge (m.sewr xr)
    by_cases hxr : xr ∈ br
    · rw [m.sewr_of_mem hxr]
      show _ = (if h : m.toDisk xr ∈ bd then _ else _)
      rw [dite_eq_left (m.toDisk_mem xr hxr), m.toRest_toDisk xr hxr]
    · rw [m.sewr_of_not_mem hxr]
      rfl
  node_r := by
    intro xr hxr
    show _ = m.sewNode (m.sewr xr)
    rw [m.sewr_of_not_mem hxr]
    rfl

end SewMatch

end FourColor
